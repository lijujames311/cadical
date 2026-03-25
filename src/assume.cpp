#include "internal.hpp"
#include "literals.hpp"
#include "options.hpp"
#include <limits>

namespace CaDiCaL {

// Failed literal handling as pioneered by MiniSAT.  This first function
// adds an assumption literal onto the assumption stack.

void Internal::assume (Lit lit) {
  if (level && !opts.ilb)
    backtrack ();
  else if (val (lit) < 0)
    backtrack_without_updating_phases (var (lit).level > 0 ? var (lit).level - 1 : 0);
  Flags &f = flags (lit);
  const unsigned char bit = bign (lit);
  if (f.assumed & bit) {
    LOG ("ignoring already assumed %s", LOGLIT(lit));
    return;
  }
  LOG ("assume %s", LOGLIT(lit));
  f.assumed |= bit;
  assumptions.push_back (lit);
  freeze (lit);
}

// for LRAT we actually need to implement recursive DFS
// for non-lrat use BFS. TODO: maybe derecursify to avoid stack overflow
//
void Internal::assume_analyze_literal (Lit lit) {
  assert (lit != INVALID_LIT);
  Flags &f = flags (lit);
  if (f.seen)
    return;
  f.seen = true;
  analyzed.push_back (lit);
  Var &v = var (lit);
  assert (val (lit) < 0);
  if (v.reason == external_reason) {
    v.reason = wrapped_learn_external_reason_clause (-lit);
    assert (v.reason || !v.level);
  }
  assert (v.reason != external_reason);
  if (!v.level) {
    int64_t id = unit_id (-lit);
    lrat_chain.push_back (id);
    return;
  }
  if (v.reason) {
    assert (v.level);
    LOG (v.reason, "analyze reason");
    for (const auto &other : *v.reason) {
      assume_analyze_literal (other);
    }
    lrat_chain.push_back (v.reason->id);
    return;
  }
  assert (assumed (-lit));
  LOG ("failed assumption %s", LOGLIT(-lit));
  clause.push_back (lit);
}

void Internal::assume_analyze_reason (Lit lit, Clause *reason) {
  assert (reason);
  assert (lrat_chain.empty ());
  assert (reason != external_reason);
  assert (lrat);
  for (const auto &other : *reason)
    if (other != lit)
      assume_analyze_literal (other);
  lrat_chain.push_back (reason->id);
}

// Find all failing assumptions starting from the one on the assumption
// stack with the lowest decision level.  This goes back to MiniSAT and is
// called 'analyze_final' there.

void Internal::failing () {

  START (analyze);

  LOG ("analyzing failing assumptions");

  assert (analyzed.empty ());
  assert (clause.empty ());
  assert (lrat_chain.empty ());
  assert (!marked_failed);
  assert (!conflict_id);

  if (!unsat_constraint) {
    // Search for failing assumptions in the (internal) assumption stack.

    // There are in essence three cases: (1) An assumption is falsified on
    // the root-level and then 'failed_unit' is set to that assumption, (2)
    // two clashing assumptions are assumed and then 'failed_clashing' is
    // set to the second assumed one, or otherwise (3) there is a failing
    // assumption 'first_failed' with minimum (non-zero) decision level
    // 'failed_level'.

    Lit failed_unit = INVALID_LIT;
    Lit failed_clashing = INVALID_LIT;
    Lit first_failed = INVALID_LIT;
    Var::Level failed_level = std::numeric_limits<Var::Level>::max ();
    ELit efailed = INVALID_ELIT;

    for (auto &elit : external->assumptions) {
      Lit lit = external->e2i[elit.labs ()];
      if (elit.is_negated ())
        lit = -lit;
      if (val (lit) >= 0)
        continue;
      const Var &v = var (lit);
      if (!v.level) {
        failed_unit = lit;
        efailed = elit;
        break;
      }
      if (failed_clashing != INVALID_LIT)
        continue;
      if (v.reason == external_reason) {
        Var &ev = var (lit);
        ev.reason = learn_external_reason_clause (-lit);
        if (!ev.reason) {
          ev.level = 0;
          failed_unit = lit;
          efailed = elit;
          break;
        }
        ev.level = 0;
        // Recalculate assignment level
        for (const auto &other : *ev.reason) {
          if (other == -lit)
            continue;
          assert (val (other));
          Var::Level tmp = var (other).level;
          if (tmp > ev.level)
            ev.level = tmp;
        }
        if (!ev.level) {
          failed_unit = lit;
          efailed = elit;
          break;
        }
      }
      assert (v.reason != external_reason);
      if (!v.reason) {
        failed_clashing = lit;
        efailed = elit;
      } else if (first_failed == INVALID_LIT || v.level < failed_level) {
        first_failed = lit;
        efailed = elit;
        failed_level = v.level;
      }
    }

    assert (clause.empty ());

    // Get the 'failed' assumption from one of the three cases.
    Lit failed;
    if (failed_unit != INVALID_LIT)
      failed = failed_unit;
    else if (failed_clashing != INVALID_LIT)
      failed = failed_clashing;
    else
      failed = first_failed;
    assert (failed != INVALID_LIT);
    assert (efailed != INVALID_ELIT);

    // In any case mark literal 'failed' as failed assumption.
    {
      Flags &f = flags (failed);
      const unsigned bit = bign (failed);
      assert (!(f.failed & bit));
      f.failed |= bit;
    }

    // First case (1).
    if (failed_unit != INVALID_LIT) {
      assert (failed == failed_unit);
      LOG ("root-level falsified assumption %s", LOGLIT(failed));
      if (proof) {
        if (lrat) {

          const int64_t id = external->external_unit_reason (efailed);
          if (id) {
            lrat_chain.push_back (id);
          } else {
            int64_t id = unit_id (-failed_unit);
            lrat_chain.push_back (id);
          }
        }
        proof->add_assumption_clause (++clause_id, -efailed, lrat_chain);
        conclusion.push_back (clause_id);
        lrat_chain.clear ();
      }
      goto DONE;
    }

    // Second case (2).
    if (failed_clashing != INVALID_LIT) {
      assert (failed == failed_clashing);
      LOG ("clashing assumptions %s and %s", LOGLIT(failed), LOGLIT(-failed));
      Flags &f = flags (-failed);
      const unsigned bit = bign (-failed);
      assert (!(f.failed & bit));
      f.failed |= bit;
      if (proof) {
        vector<ELit> clash = {externalize (failed), externalize (-failed)};
        proof->add_assumption_clause (++clause_id, clash, lrat_chain);
        conclusion.push_back (clause_id);
      }
      goto DONE;
    }

    // Fall through to third case (3).
    LOG ("starting with assumption %s falsified on minimum decision level "
         "%" LEVEL,
         LOGLIT (first_failed), failed_level);

    assert (first_failed != INVALID_LIT);
    assert (failed_level > 0);

    // The 'analyzed' stack serves as working stack for a BFS through the
    // implication graph until decisions, which are all assumptions, or
    // units are reached.  This is simpler than corresponding code in
    // 'analyze'.
    {
      LOG ("failed assumption %s", LOGLIT(first_failed));
      Flags &f = flags (first_failed);
      assert (!f.seen);
      f.seen = true;
      assert (f.failed & bign (first_failed));
      analyzed.push_back (-first_failed);
      clause.push_back (-first_failed);
    }
  } else {
    // unsat_constraint
    // The assumptions necessary to fail each literal in the constraint are
    // collected.
    for (auto lit : constraint) {
      lit = -1 * lit;
      assert (lit != OTHER_INVALID_LIT);
      flags (lit).seen = true;
      analyzed.push_back (lit);
    }
  }

  {
    // used for unsat_constraint lrat
    vector<vector<int64_t>> constraint_chains;
    vector<vector<Lit>> constraint_clauses;
    vector<Lit> sum_constraints;
    vector<ELit> econstraints;
    for (auto &elit : external->constraint) {
      Lit lit = external->e2i[elit.labs ()];
      if (elit.is_negated ())
        lit = -lit;
      if (lit == INVALID_LIT)
        continue;
      Flags &f = flags (lit);
      if (f.seen)
        continue;
      if (std::find (econstraints.begin (), econstraints.end (), elit) !=
          econstraints.end ())
        continue;
      econstraints.push_back (elit);
    }

    // no LRAT do bfs as it was before
    if (!lrat) {
      size_t next = 0;
      while (next < analyzed.size ()) {
        const Lit lit = analyzed[next++];
        assert (val (lit) > 0);
        Var &v = var (lit);
        if (!v.level)
          continue;
        if (v.reason == external_reason) {
          v.reason = wrapped_learn_external_reason_clause (lit);
          if (!v.reason) {
            v.level = 0;
            continue;
          }
        }
        assert (v.reason != external_reason);
        if (v.reason) {
          assert (v.level);
          LOG (v.reason, "analyze reason");
          for (const auto &other : *v.reason) {
            Flags &f = flags (other);
            if (f.seen)
              continue;
            f.seen = true;
            assert (val (other) < 0);
            analyzed.push_back (-other);
          }
        } else {
          assert (assumed (lit));
          LOG ("failed assumption %s", LOGLIT(lit));
          clause.push_back (-lit);
          Flags &f = flags (lit);
          const unsigned bit = bign (lit);
          assert (!(f.failed & bit));
          f.failed |= bit;
        }
      }
      clear_analyzed_literals ();
    } else if (!unsat_constraint) { // LRAT for case (3)
      assert (clause.size () == 1);
      const Lit lit = clause[0];
      Var &v = var (lit);
      assert (v.reason);
      if (v.reason == external_reason) { // does this even happen?
        v.reason = wrapped_learn_external_reason_clause (lit);
      }
      assert (v.reason != external_reason);
      if (v.reason)
        assume_analyze_reason (lit, v.reason);
      else {
        int64_t id = unit_id (lit);
        lrat_chain.push_back (id);
      }
      for (auto &lit : clause) {
        Flags &f = flags (lit);
        const unsigned bit = bign (-lit);
        if (!(f.failed & bit))
          f.failed |= bit;
      }
      clear_analyzed_literals ();
    } else { // LRAT for unsat_constraint
      assert (clause.empty ());
      clear_analyzed_literals ();
      for (auto lit : constraint) {
        // make sure nothing gets marked failed twice
        // also might shortcut the case where
        // lrat_chain is empty because clause is tautological
        assert (lit != OTHER_INVALID_LIT);
        assume_analyze_literal (lit);
        vector<int64_t> empty;
        vector<Lit> empty2;
        constraint_chains.push_back (empty);
        constraint_clauses.push_back (empty2);
        for (auto ign : clause) {
          constraint_clauses.back ().push_back (ign);
          Flags &f = flags (ign);
          const unsigned bit = bign (-ign);
          if (!(f.failed & bit)) {
            sum_constraints.push_back (ign);
            assert (!(f.failed & bit));
            f.failed |= bit;
          }
        }
        clause.clear ();
        clear_analyzed_literals ();
        for (auto p : lrat_chain) {
          constraint_chains.back ().push_back (p);
        }
        lrat_chain.clear ();
      }
      for (auto &lit : sum_constraints)
        clause.push_back (lit);
    }
    clear_analyzed_literals ();

    // Doing clause minimization here does not do anything because
    // the clause already contains only one literal of each level
    // and minimization can never reduce the number of levels

    VERBOSE (1, "found %zd failed assumptions %.0f%%", clause.size (),
             percent (clause.size (), assumptions.size ()));

    // We do not actually need to learn this clause, since the conflict is
    // forced already by some other clauses.  There is also no bumping
    // of variables nor clauses necessary.  But we still want to check
    // correctness of the claim that the determined subset of failing
    // assumptions are a high-level core or equivalently their negations
    // form a unit-implied clause.
    //
    if (!unsat_constraint) {
      external->check_learned_clause ();
      if (proof) {
        vector<ELit> eclause;
        for (auto &lit : clause)
          eclause.push_back (externalize (lit));
        proof->add_assumption_clause (++clause_id, eclause, lrat_chain);
        conclusion.push_back (clause_id);
      }
    } else {
      assert (!lrat || (constraint.size () == constraint_clauses.size () &&
                        constraint.size () == constraint_chains.size ()));
      for (auto p = constraint.rbegin (); p != constraint.rend (); p++) {
        const auto &lit = *p;
        if (lrat) {
          clause.clear ();
          for (auto &ign : constraint_clauses.back ())
            clause.push_back (ign);
          constraint_clauses.pop_back ();
        }
        clause.push_back (-lit);
        external->check_learned_clause ();
        if (proof) {
          if (lrat) {
            for (auto p : constraint_chains.back ()) {
              lrat_chain.push_back (p);
            }
            constraint_chains.pop_back ();
            LOG (lrat_chain, "assume proof chain with constraints");
          }
          vector<ELit> eclause;
          for (auto &lit : clause)
            eclause.push_back (externalize (lit));
          proof->add_assumption_clause (++clause_id, eclause, lrat_chain);
          conclusion.push_back (clause_id);
          lrat_chain.clear ();
        }
        clause.pop_back ();
      }
      if (proof) {
        for (auto &elit : econstraints) {
          if (lrat) {

            const int64_t id = external->external_unit_reason (elit);
            if (id) {
              lrat_chain.push_back (id);
            } else {
              Lit lit = external->e2i[elit.labs ()];
              if (elit.is_negated ())
                lit = -lit;
              int64_t id = unit_id (-lit);
              lrat_chain.push_back (id);
            }
          }
          proof->add_assumption_clause (++clause_id, -elit, lrat_chain);
          conclusion.push_back (clause_id);
          lrat_chain.clear ();
        }
      }
    }
    lrat_chain.clear ();
    clause.clear ();
  }

DONE:

  STOP (analyze);
}

bool Internal::failed (Lit lit) {
  if (!marked_failed) {
    if (!conflict_id)
      failing ();
    marked_failed = true;
  }
  conclude_unsat ();
  Flags &f = flags (lit);
  const unsigned bit = bign (lit);
  return (f.failed & bit) != 0;
}

void Internal::conclude_unsat () {
  if (!proof || concluded)
    return;
  concluded = true;
  if (!marked_failed) {
    assert (conclusion.empty ());
    if (!conflict_id)
      failing ();
    marked_failed = true;
  }
  ConclusionType con;
  if (conflict_id)
    con = CONFLICT;
  else if (unsat_constraint)
    con = CONSTRAINT;
  else
    con = ASSUMPTIONS;
  proof->conclude_unsat (con, conclusion);
}

void Internal::reset_concluded () {
  if (proof)
    proof->reset_assumptions ();
  if (concluded) {
    LOG ("reset concluded");
    concluded = false;
  }
  if (conflict_id) {
    assert (conclusion.size () == 1);
    return;
  }
  conclusion.clear ();
}

// Add the start of each incremental phase (leaving the state
// 'UNSATISFIABLE' actually) we reset all assumptions.

void Internal::reset_assumptions () {
  for (const auto &lit : assumptions) {
    Flags &f = flags (lit);
    const unsigned char bit = bign (lit);
    f.assumed &= ~bit;
    f.failed &= ~bit;
    melt (lit);
  }
  LOG ("cleared %zd assumptions", assumptions.size ());
  assumptions.clear ();
  marked_failed = true;
}

struct sort_assumptions_positive_rank {
  Internal *internal;

  // Decision level could be 'INT_MAX' and thus 'level + 1' could overflow.
  // Therefore we carefully have to use 'unsigned' for levels below.

  const unsigned max_level;

  sort_assumptions_positive_rank (Internal *s)
      : internal (s), max_level (s->level + 1u) {}

  typedef uint64_t Type;

  // Set assumptions first, then sorted by position on the trail
  // unset literals are sorted by literal value.

  Type operator() (const Lit &a) const {
    const int val = internal->val (a);
    const bool assigned = (val != 0);
    const Var &v = internal->var (a);
    uint64_t res = (assigned ? (unsigned) v.level : max_level);
    res <<= 32;
    res |= (assigned ? v.trail : a.var());
    return res;
  }
};

struct sort_assumptions_smaller {
  Internal *internal;
  sort_assumptions_smaller (Internal *s) : internal (s) {}
  bool operator() (const Lit &a, const Lit &b) const {
    return sort_assumptions_positive_rank (internal) (a) <
           sort_assumptions_positive_rank (internal) (b);
  }
};

// Sort the assumptions by the current position on the trail and backtrack
// to the first place where the assumptions and the current trail differ.

void Internal::sort_and_reuse_assumptions () {
  assert (opts.ilb >= 1);
  if (assumptions.empty ()) {
    if (opts.ilb == 1) {
      LOG ("no assumptions, reusing nothing (ilb == 1)");
      backtrack (0);
    } else { // reuse full trail
      LOG ("no assumptions, reusing everything (ilb == 2)");
      return;
    }
  }
  MSORT (opts.radixsortlim, assumptions.begin (), assumptions.end (),
         sort_assumptions_positive_rank (this),
         sort_assumptions_smaller (this));

  Var::Level max_level = 0;
  // assumptions are sorted by level, with unset at the end
  for (auto lit : assumptions) {
    if (val (lit))
      max_level = var (lit).level;
    else
      break;
  }

  const Var::Level size = min (level + 1, max_level + 1);
  assert ((size_t) level == control.size () - 1);
  LOG (assumptions, "sorted assumptions");
  Var::Level target = 0;
  for (Var::Level i = 1, j = 0; i < size;) {
    const Level &l = control[i];
    const Lit lit = l.decision;
    const Lit alit = assumptions[j];
    const Var::Level lev = i;
    target = lev;
    if (val (alit) > 0 &&
        var (alit).level < lev) { // we can ignore propagated assumptions
      LOG ("ILB skipping propagation %s", LOGLIT(alit));
      ++j;
      continue;
    }
    if (lit == INVALID_LIT) { // skip fake decisions
      target = lev - 1;
      break;
    }
    ++i, ++j;
    assert (var (lit).level == lev);
    if (l.decision == alit) {
      continue;
    }
    target = lev - 1;
    LOG ("first different literal %s on the trail and %s from the "
         "assumptions",
         LOGLIT(lit), LOGLIT(alit));
    break;
  }
  if (opts.ilb == 1 &&
      (size_t) target > assumptions.size ()) // reusing only assumptions
    target = assumptions.size ();
  if (target < level)
    backtrack_without_updating_phases (target);
  LOG ("assumptions allow for reuse of trail up to level %" LEVEL, level);
  if ((size_t) level > assumptions.size ())
    stats.assumptionsreused += assumptions.size ();
  else
    stats.assumptionsreused += level;
}
} // namespace CaDiCaL
