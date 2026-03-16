#include "internal.hpp"
#include "literals.hpp"
#include <complex.h>

namespace CaDiCaL {

struct literal_occ {
  Lit lit;
  int count;
  bool operator< (const literal_occ &locc) const {
    return (count > locc.count) || (count == locc.count && lit < locc.lit);
  }
  literal_occ operator++ () {
    ++count;
    return *this;
  }
};

std::vector<Lit> Internal::lookahead_populate_locc () {
  std::vector<literal_occ> loccs ((std::size_t) max_var + 1);
  for (auto v : vars)
    loccs[v.var ()].lit = v;
  for (const auto &c : clauses)
    if (!c->redundant)
      for (const auto &lit : *c)
        if (active (lit))
          ++loccs[lit.var ()];
  std::sort (begin (loccs), end (loccs));
  std::vector<Lit> locc_map;
  locc_map.reserve (max_var);
  for (const auto &locc : loccs)
    locc_map.push_back (locc.lit);
  return locc_map;
}

Lit Internal::lookahead_locc (const std::vector<Lit> &loccs) {
  for (auto lit : loccs)
    if (active (lit) && !assumed (lit) && !assumed (-lit) &&
        !val (lit))
      return lit;
  return INVALID_LIT;
}

// This calculates the literal that appears the most often reusing the
// available datastructures and iterating over the clause set. This is too
// slow to be called iteratively. A faster (but inexact) version is
// lookahead_populate_loc and lookahead_loc.
Lit Internal::most_occurring_literal () {
  init_noccs ();
  for (const auto &c : clauses)
    if (!c->redundant)
      for (const auto &lit : *c)
        if (active (lit))
          noccs (lit)++;
  int64_t max_noccs = 0;
  Lit res = INVALID_LIT;

  if (unsat)
    return OTHER_INVALID_LIT;

  propagate ();
  for (auto idx : vars) {
    if (!active (idx) || assumed (idx) || assumed (-idx) || val (idx))
      continue;
    for (int sign = -1; sign <= 1; sign += 2) {
      const Lit lit = sign * idx;
      if (!active (lit))
        continue;
      int64_t tmp = noccs (lit);
      if (tmp <= max_noccs)
        continue;
      max_noccs = tmp;
      res = lit;
    }
  }
  LOG ("maximum occurrence %" PRId64 " of literal %s", max_noccs, LOGLIT(res));
  reset_noccs ();
  return res;
}

// We probe on literals first, which occur more often negated and thus we
// sort the 'probes' stack in such a way that literals which occur negated
// less frequently come first.  Probes are taken from the back of the stack.

struct probe_negated_noccs_rank {
  Internal *internal;
  probe_negated_noccs_rank (Internal *i) : internal (i) {}
  typedef size_t Type;
  Type operator() (Lit a) const { return internal->noccs (-a); }
};

// Follow the ideas in 'generate_probes' but flush non root probes and
// reorder remaining probes.

void Internal::lookahead_flush_probes () {

  assert (!probes.empty ());

  init_noccs ();
  for (const auto &c : clauses) {
    Lit a, b;
    if (!is_binary_clause (c, a, b))
      continue;
    noccs (a)++;
    noccs (b)++;
  }

  const auto eop = probes.end ();
  auto j = probes.begin ();
  for (auto i = j; i != eop; i++) {
    Lit lit = *i;
    if (!active (lit))
      continue;
    const bool have_pos_bin_occs = noccs (lit) > 0;
    const bool have_neg_bin_occs = noccs (-lit) > 0;
    if (have_pos_bin_occs == have_neg_bin_occs)
      continue;
    if (have_pos_bin_occs)
      lit = -lit;
    assert (!noccs (lit)), assert (noccs (-lit) > 0);
    if (propfixed (lit) >= stats.all.fixed)
      continue;
    LOG ("keeping probe %s negated occs %" PRId64 "", LOGLIT(lit), noccs (-lit));
    *j++ = lit;
  }
  size_t remain = j - probes.begin ();
#ifndef QUIET
  size_t flushed = probes.size () - remain;
#endif
  probes.resize (remain);

  rsort (probes.begin (), probes.end (), probe_negated_noccs_rank (this));

  reset_noccs ();
  shrink_vector (probes);

  PHASE ("probe-round", stats.probingrounds,
         "flushed %zd literals %.0f%% remaining %zd", flushed,
         percent (flushed, remain + flushed), remain);
}

void Internal::lookahead_generate_probes () {

  assert (probes.empty ());

  // First determine all the literals which occur in binary clauses. It is
  // way faster to go over the clauses once, instead of walking the watch
  // lists for each literal.
  //
  init_noccs ();
  for (const auto &c : clauses) {
    Lit a, b;
    if (!is_binary_clause (c, a, b))
      continue;
    noccs (a)++;
    noccs (b)++;
  }

  for (auto idx: vars) {

    // Then focus on roots of the binary implication graph, which are
    // literals occurring negatively in a binary clause, but not positively.
    // If neither 'idx' nor '-idx' is a root it makes less sense to probe
    // this variable.

    // This argument requires that equivalent literal substitution through
    // 'decompose' is performed, because otherwise there might be 'cyclic
    // roots' which are not tried, i.e., -1 2 0, 1 -2 0, 1 2 3 0, 1 2 -3 0.

    const bool have_pos_bin_occs = noccs (idx) > 0;
    const bool have_neg_bin_occs = noccs (-idx) > 0;

    // if (have_pos_bin_occs == have_neg_bin_occs) continue;

    if (have_pos_bin_occs) {
      Lit probe = -idx;

      // See the discussion where 'propfixed' is used below.
      //
      if (propfixed (probe) >= stats.all.fixed)
        continue;

      LOG ("scheduling probe %s negated occs %" PRId64 "", LOGLIT(probe),
           noccs (-probe));
      probes.push_back (probe);
    }

    if (have_neg_bin_occs) {
      Lit probe = idx;

      // See the discussion where 'propfixed' is used below.
      //
      if (propfixed (probe) >= stats.all.fixed)
        continue;

      LOG ("scheduling probe %s negated occs %" PRId64 "", LOGLIT(probe),
           noccs (-probe));
      probes.push_back (probe);
    }
  }

  rsort (probes.begin (), probes.end (), probe_negated_noccs_rank (this));

  reset_noccs ();
  shrink_vector (probes);

  PHASE ("probe-round", stats.probingrounds,
         "scheduled %zd literals %.0f%%", probes.size (),
         percent (probes.size (), 2 * max_var));
}

Lit Internal::lookahead_next_probe () {

  int generated = 0;

  for (;;) {

    if (probes.empty ()) {
      if (generated++)
        return INVALID_LIT;
      lookahead_generate_probes ();
    }

    while (!probes.empty ()) {

      Lit probe = probes.back ();
      probes.pop_back ();

      // Eliminated or assigned.
      //
      if (!active (probe) || assumed (probe) || assumed (-probe))
        continue;

      // There is now new unit since the last time we propagated this probe,
      // thus we propagated it before without obtaining a conflict and
      // nothing changed since then.  Thus there is no need to propagate it
      // again.  This observation was independently made by Partik Simons
      // et.al. in the context of implementing 'smodels' (see for instance
      // Alg. 4 in his JAIR article from 2002) and it has also been
      // contributed to the thesis work of Yacine Boufkhad.
      //
      if (propfixed (probe) >= stats.all.fixed)
        continue;

      return probe;
    }
  }
}

bool non_tautological_cube (std::vector<Lit> cube) {
  std::sort (begin (cube), end (cube), clause_lit_less_than ());

  for (size_t i = 0, j = 1; j < cube.size (); ++i, ++j)
    if (cube[i] == cube[j])
      return false;
    else if (cube[i] == -cube[j])
      return false;
    else if (cube[i] == INVALID_LIT)
      return false;

  return true;
}

bool Internal::terminating_asked () {

  if (external->terminator && external->terminator->terminate ()) {
    MSG ("connected terminator forces termination");
    return true;
  }

  if (termination_forced) {
    MSG ("termination forced");
    return true;
  }
  return false;
}

// We run probing on all literals with some differences:
//
// * no limit on the number of propagations. We rely on terminating to
// stop()
// * we run only one round
//
// The run can be expensive, so we actually first run the cheaper
// occurrence version and only then run lookahead.
//
Lit Internal::lookahead_probing () {

  if (!active ())
    return INVALID_LIT;

  MSG ("lookahead-probe-round %" PRId64
       " without propagations limit and %zu assumptions",
       stats.probingrounds, assumptions.size ());

  termination_forced = false;

#ifndef QUIET
  int old_failed = stats.failed;
  int64_t old_probed = stats.probed;
#endif
  int64_t old_hbrs = stats.hbrs;

  if (unsat)
    return OTHER_INVALID_LIT;
  if (level)
    backtrack_without_updating_phases ();
  if (!propagate ()) {
    MSG ("empty clause before probing");
    learn_empty_clause ();
    return OTHER_INVALID_LIT;
  }

  if (terminating_asked ())
    return most_occurring_literal ();

  decompose ();

  if (ternary ()) // If we derived a binary clause
    decompose (); // then start another round of ELS.

  // Remove duplicated binary clauses and perform in essence hyper unary
  // resolution, i.e., derive the unit '2' from '1 2' and '-1 2'.
  //
  mark_duplicated_binary_clauses_as_garbage ();

  lim.conflicts = -1;

  if (!probes.empty ())
    lookahead_flush_probes ();

  // We reset 'propfixed' since there was at least another conflict thus
  // a new learned clause, which might produce new propagations (and hyper
  // binary resolvents).  During 'generate_probes' we keep the old value.
  //
  for (auto idx : vars)
    propfixed (idx) = propfixed (-idx) = -1;

  assert (unsat || propagated == trail.size ());
  propagated = propagated2 = trail.size ();

  Lit probe;
  Lit res = most_occurring_literal ();
  int max_hbrs = -1;

  set_mode (PROBE);

  MSG ("unsat = %d, terminating_asked () = %d ", unsat,
       terminating_asked ());
  init_probehbr_lrat ();
  while (!unsat && !terminating_asked () &&
         (probe = lookahead_next_probe ()) != INVALID_LIT) {
    stats.probed++;
    int hbrs;

    probe_assign_decision (probe);
    if (probe_propagate ())
      hbrs = trail.size (), backtrack ();
    else
      hbrs = 0, failed_literal (probe);
    clean_probehbr_lrat ();
    if (max_hbrs < hbrs ||
        (max_hbrs == hbrs &&
         internal->bumped (probe) > internal->bumped (res))) {
      res = probe;
      max_hbrs = hbrs;
    }
  }

  reset_mode (PROBE);

  if (unsat) {
    MSG ("probing derived empty clause");
    res = OTHER_INVALID_LIT;
  } else if (propagated < trail.size ()) {
    MSG ("probing produced %zd units",
         (size_t) (trail.size () - propagated));
    if (!propagate ()) {
      MSG ("propagating units after probing results in empty clause");
      learn_empty_clause ();
      res = OTHER_INVALID_LIT;
    } else
      sort_watches ();
  }

#ifndef QUIET
  int failed = stats.failed - old_failed;
  int64_t probed = stats.probed - old_probed;
#endif
  int64_t hbrs = stats.hbrs - old_hbrs;

  MSG ("lookahead-probe-round %" PRId64 " probed %" PRId64
       " and found %d failed literals",
       stats.probingrounds, probed, failed);

  if (hbrs)
    PHASE ("lookahead-probe-round", stats.probingrounds,
           "found %" PRId64 " hyper binary resolvents", hbrs);

  LOG ("lookahead literal %s with %d", LOGLIT(res), max_hbrs);

  return res;
}

InternalCubesWithStatus Internal::generate_cubes (int depth, int min_depth) {
  if (!active () || depth == 0) {
    InternalCubesWithStatus cubes;
    cubes.status = 0;
    cubes.cubes.push_back (std::vector<Lit> ());
    return cubes;
  }

  lookingahead = true;
  START (lookahead);
  MSG ("Generating cubes of depth %i", depth);

  // presimplify required due to assumptions

  termination_forced = false;
  int res = already_solved ();
  if (res == 0)
    res = restore_clauses ();
  if (unsat)
    res = 10;
  if (res != 0)
    res = solve (true);
  if (res != 0) {
    MSG ("Solved during preprocessing");
    InternalCubesWithStatus cubes;
    cubes.status = res;
    lookingahead = false;
    STOP (lookahead);
    return cubes;
  }

  reset_limits ();
  MSG ("generate cubes with %zu assumptions\n", assumptions.size ());

  assert (ntab.empty ());
  std::vector<Lit> current_assumptions{assumptions};
  std::vector<std::vector<Lit>> cubes{{assumptions}};
  auto loccs{lookahead_populate_locc ()};
  LOG ("loccs populated\n");
  assert (ntab.empty ());

  for (int i = 0; i < depth; ++i) {
    LOG ("Probing at depth %i, currently %zu have been generated", i,
         cubes.size ());
    std::vector<std::vector<Lit>> cubes2{std::move (cubes)};
    cubes.clear ();

    for (size_t j = 0; j < cubes2.size (); ++j) {
      assert (ntab.empty ());
      assert (!unsat);
      reset_assumptions ();
      for (auto lit : cubes2[j])
        assume (lit);
      restore_clauses ();
      propagate ();
      // preprocess_round(0); //uncomment maybe

      if (unsat) {
        LOG ("current cube is unsat; skipping");
        unsat = false;
        continue;
      }

      Lit res = terminating_asked () ? lookahead_locc (loccs)
                                     : lookahead_probing ();
      if (unsat) {
        LOG ("current cube is unsat; skipping");
        unsat = false;
        continue;
      }

      if (res == INVALID_LIT) {
        LOG ("no lit to split %s", LOGLIT(res));
        cubes.push_back (cubes2[j]);
        continue;
      }

      assert (res != INVALID_LIT);
      LOG ("splitting on lit %s", LOGLIT(res));
      std::vector<Lit> cube1{cubes2[j]};
      cube1.push_back (res);
      std::vector<Lit> cube2{std::move (cubes2[j])};
      cube2.push_back (-res);
      cubes.push_back (cube1);
      cubes.push_back (cube2);
    }

    if (terminating_asked () && i >= min_depth)
      break;
  }

  assert (std::for_each (
      std::begin (cubes), std::end (cubes),
      [] (std::vector<Lit> cube) { return non_tautological_cube (cube); }));
  reset_assumptions ();

  for (auto lit : current_assumptions)
    assume (lit);

  STOP (lookahead);
  lookingahead = false;

  if (unsat) {
    LOG ("Solved during preprocessing");
    InternalCubesWithStatus cubes;
    cubes.status = 20;
    return cubes;
  }

  InternalCubesWithStatus rcubes;
  rcubes.status = 0;
  rcubes.cubes = cubes;

  return rcubes;
}

} // namespace CaDiCaL
