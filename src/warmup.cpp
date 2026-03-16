#include "cadical.hpp"
#include "internal.hpp"
#include "literals.hpp"

namespace CaDiCaL {

// The idea of warmup is to reuse the strength of CDCL, namely
// propagating, before calling random walk that is not good at
// propagating long chains. Therefore, we propagate (ignoring all conflicts)
// discovered along the way.
// The asignmend is the same as the normal assignment however, it updates
// the target phases so that local search can pick them up later

// specific warmup version with saving of the target.
inline void Internal::warmup_assign (Lit lit, Clause *reason) {

  assert (level); // no need to learn unit clauses here
  require_mode (SEARCH);

  const int idx = vidx (lit);
  assert (reason != external_reason);
  assert (!vals[idx]);
  assert (!flags (lit).eliminated () || reason == decision_reason);
  assert (!searching_lucky_phases);
  assert (lrat_chain.empty ());
  Var &v = var (lit);
  int lit_level;
  assert (
      !(reason == external_reason &&
        ((size_t) level <= assumptions.size () + (!!constraint.size ()))));
  assert (reason);
  assert (level || reason == decision_reason);
  // we  purely assign in order here
  lit_level = level;

  v.level = lit_level;
  v.trail = get_trail_size ();
  v.reason = reason;
  assert ((int) num_assigned < max_var);
  assert (num_assigned == trail.size ());
  num_assigned++;
  const signed char tmp = sign (lit);
  phases.saved[idx] = tmp;
  set_val (Lit (idx), tmp);
  assert (val (lit) > 0);
  assert (val (-lit) < 0);

  trail.push_back (lit);
#ifdef LOGGING
  if (!lit_level)
    LOG ("root-level unit assign %s @ 0", LOGLIT(lit));
  else
    LOG (reason, "search assign %s @ %d", LOGLIT(lit), lit_level);
#endif

  assert (watching ());
  const Watches &ws = watches (-lit);
  if (!ws.empty ()) {
    const Watch &w = ws[0];
    __builtin_prefetch (&w, 0, 1);
  }
}

void Internal::warmup_propagate_beyond_conflict () {

  assert (!unsat);

  START (propagate);
  assert (!ignore);

  int64_t before = propagated;

  while (propagated != trail.size ()) {

    const Lit lit = -trail[propagated++];
    LOG ("propagating %s", LOGLIT(-lit));
    Watches &ws = watches (lit);

    const const_watch_iterator eow = ws.end ();
    watch_iterator j = ws.begin ();
    const_watch_iterator i = j;

    while (i != eow) {

      const Watch w = *j++ = *i++;
      const signed char b = val (w.blit);

      if (b > 0)
        continue; // blocking literal satisfied

      if (w.binary ()) {

        // In principle we can ignore garbage binary clauses too, but that
        // would require to dereference the clause pointer all the time with
        //
        // if (w.clause->garbage) { j--; continue; } // (*)
        //
        // This is too costly.  It is however necessary to produce correct
        // proof traces if binary clauses are traced to be deleted ('d ...'
        // line) immediately as soon they are marked as garbage.  Actually
        // finding instances where this happens is pretty difficult (six
        // parallel fuzzing jobs in parallel took an hour), but it does
        // occur.  Our strategy to avoid generating incorrect proofs now is
        // to delay tracing the deletion of binary clauses marked as garbage
        // until they are really deleted from memory.  For large clauses
        // this is not necessary since we have to access the clause anyhow.
        //
        // Thanks go to Mathias Fleury, who wanted me to explain why the
        // line '(*)' above was in the code. Removing it actually really
        // improved running times and thus I tried to find concrete
        // instances where this happens (which I found), and then
        // implemented the described fix.

        // Binary clauses are treated separately since they do not require
        // to access the clause at all (only during conflict analysis, and
        // there also only to simplify the code).

        if (b < 0)
          // ignoring conflict
          ++stats.warmup.conflicts;
        else {
          warmup_assign (w.blit, w.clause);
        }

      } else {
        assert (w.clause->size > 2);

        // The cache line with the clause data is forced to be loaded here
        // and thus this first memory access below is the real hot-spot of
        // the solver.  Note, that this check is positive very rarely and
        // thus branch prediction should be almost perfect here.

        if (w.clause->garbage) {
          j--;
          continue;
        }
        literal_iterator lits = w.clause->begin ();
        const Lit other = lits[0] ^ lits[1] ^ lit;
        const signed char u = val (other);
        if (u > 0)
          j[-1].blit = other;
        else {
          const int size = w.clause->size;
          const const_literal_iterator end = lits + size;
          const literal_iterator middle = lits + w.clause->pos;
          literal_iterator k = middle;
          signed char v = -1;
          Lit r = INVALID_LIT;
          while (k != end && (v = val (r = *k)) < 0)
            k++;
          if (v < 0) {
            k = lits + 2;
            assert (w.clause->pos <= size);
            while (k != middle && (v = val (r = *k)) < 0)
              k++;
          }
#if 0 // my intuiton: does not make sense to update here
          w.clause->pos = k - lits; // always save position
#endif
          assert (lits + 2 <= k), assert (k <= w.clause->end ());

          if (v > 0) {

            // Replacement satisfied, so just replace 'blit'.

            j[-1].blit = r;

          } else if (!v) {

            // Found new unassigned replacement literal to be watched.

            LOG (w.clause, "unwatch %s in", LOGLIT(r));

            lits[0] = other;
            lits[1] = r;
            *k = lit;

            watch_literal (r, lit, w.clause);

            j--; // Drop this watch from the watch list of 'lit'.

          } else if (!u) {

            assert (v < 0);

            // The other watch is unassigned ('!u') and all other literals
            // assigned to false (still 'v < 0'), thus we found a unit.
            //
            build_chain_for_units (other, w.clause, 0);
            warmup_assign (other, w.clause);
          } else {
            assert (u < 0);
            assert (v < 0);

            // ignoring conflict
            ++stats.warmup.conflicts;
          }
        }
      }
    }

    if (j != i) {
      ws.resize (j - ws.begin ());
    }
  }

  assert (propagated == trail.size ());

  stats.warmup.propagated += (trail.size () - before);
  STOP (propagate);
}

int Internal::warmup_decide_assumptions () {
  assert (!satisfied ());
  START (decide);
  int res = 0;
  if ((size_t) level < assumptions.size ()) {
    const Lit lit = assumptions[level];
    assert (assumed (lit));
    const signed char tmp = val (lit);
    if (tmp < 0) {
      LOG ("assumption %s falsified", LOGLIT(lit));
      res = 20;
    } else if (tmp > 0) {
      LOG ("assumption %s already satisfied", LOGLIT(lit));
      new_trail_level (INVALID_LIT);
      LOG ("added pseudo decision level");
    } else {
      LOG ("deciding assumption %s", LOGLIT(lit));
      search_assume_decision (lit);
    }
  } else if ((size_t) level == assumptions.size () && constraint.size ()) {

    Lit satisfied_lit = INVALID_LIT;  // The literal satisfying the constrain.
    Lit unassigned_lit = INVALID_LIT; // Highest score unassigned literal.
    Lit previous_lit = INVALID_LIT;   // Move satisfied literals to the front.

    const size_t size_constraint = constraint.size ();

#ifndef NDEBUG
    unsigned sum = 0;
    for (auto lit : constraint)
      sum += lit.signed_representation();
#endif
    for (size_t i = 0; i != size_constraint; i++) {

      // Get literal and move 'constraint[i] = constraint[i-1]'.

      Lit lit = constraint[i];
      constraint[i] = previous_lit;
      previous_lit = lit;

      const signed char tmp = val (lit);
      if (tmp < 0) {
        LOG ("constraint literal %s falsified", LOGLIT(lit));
        continue;
      }

      if (tmp > 0) {
        LOG ("constraint literal %s satisfied", LOGLIT(lit));
        satisfied_lit = lit;
        break;
      }

      assert (!tmp);
      LOG ("constraint literal %s unassigned", LOGLIT(lit));

      if (unassigned_lit == INVALID_LIT || better_decision (lit, unassigned_lit))
        unassigned_lit = lit;
    }

    if (satisfied_lit != INVALID_LIT) {

      constraint[0] = satisfied_lit; // Move satisfied to the front.

      LOG ("literal %s satisfies constraint and "
           "is implied by assumptions",
           LOGLIT(satisfied_lit));

      new_trail_level (INVALID_LIT);
      LOG ("added pseudo decision level for constraint");
      notify_decision ();

    } else {

      // Just move all the literals back.  If we found an unsatisfied
      // literal then it will be satisfied (most likely) at the next
      // decision and moved then to the first position.

      if (size_constraint) {

        for (size_t i = 0; i + 1 != size_constraint; i++)
          constraint[i] = constraint[i + 1];

        constraint[size_constraint - 1] = previous_lit;
      }

      if (unassigned_lit != INVALID_LIT) {

        LOG ("deciding %s to satisfy constraint", LOGLIT(unassigned_lit));
        search_assume_decision (unassigned_lit);

      } else {

        LOG ("failing constraint");
        unsat_constraint = true;
        res = 20;
      }
    }

#ifndef NDEBUG
    for (auto lit : constraint)
      sum -= lit.signed_representation();
    assert (!sum); // Checksum of literal should not change!
#endif

  } else {
    assert (false);
  }
  if (res)
    marked_failed = false;
  STOP (decide);
  return res;
}

void Internal::warmup_decide () {
  assert (!satisfied ());
  START (decide);
  assert ((size_t) level >= assumptions.size ());
  assert (!constraint.size () || (size_t) level > assumptions.size ());
  const bool target = (stable || opts.target == 2);
  stats.warmup.decision++;
  Lit idx = next_decision_variable ();
  if (flags (idx).eliminated ())
    ++stats.warmup.dummydecision;
  Lit decision = decide_phase (idx, target);
  new_trail_level (decision);
  warmup_assign (decision, decision_reason);
  STOP (decide);
}

int Internal::decide_and_propagate_all_assumptions (std::vector<Lit> &set_literals) {
  LOG ("decide and propagate all assumptions to fill the vectors");
  assert (!private_steps);
  int res = 0;
  int last_assumption_level = assumptions.size ();
  if (!last_assumption_level)
    return res;
  if (constraint.size ())
    last_assumption_level++;
  while (!res) {
    if (unsat)
      res = 20;
    else if (unsat_constraint)
      res = 20;
    else if (!propagate ()) {
      // let analyze run to get failed assumptions
      if (!unsat)
        analyze ();
      else
       break;
    } else if (satisfied ()) {
      assert (!res);
      if (external) {
        LOG ("found satisfied assignment ignoring the external propagator, so probably not valid");
      } else {
        res = 10;
      }
      break;
    } else {
      if (level >= last_assumption_level)
        break;
      notify_assignments ();
      res = decide ();
    }
  }

  if (unsat || unsat_constraint)
    res = 20;


  set_literals.reserve(trail.size ());
  for (auto lit: trail)
    set_literals.push_back(lit);
  if (!res) {
    // we need to repropagate now due to out-of-order units and renotify them
    backtrack ();
    if (propagated < trail.size () && !propagate ()) {
      LOG ("empty clause after root level propagation");
      learn_empty_clause ();
      res = 20;
    }
  } else {
    assert (res == 20);
    notify_assignments ();
  }
  return res;
}

int Internal::warmup () {
  assert (!unsat);
  assert (!level);
  if (!opts.warmup)
    return 0;
  require_mode (WALK);
  START (warmup);
  ++stats.warmup.count;
  int res = 0;

#ifndef QUIET
  const int64_t warmup_propagated = stats.warmup.propagated;
  const int64_t decision = stats.warmup.decision;
  const int64_t dummydecision = stats.warmup.dummydecision;
#endif
  LOG ("starting warmup");

  // first propagate assumptions in case we find a conflict. One subtle
  // thing, if we find a conflict in the assumption, then we actually do
  // need the notifications. Otherwise, we there should be no notification
  // at all (not even the `backtrack ()` at the end). Also, we cannot not
  // ignore conflicts at all, meaning that we cannot use our special
  // propagation function, even if it could counts ticks.
  const size_t assms_contraint_level =
      assumptions.size () + !constraint.empty ();
  while (!res && !conflict && (size_t) level < assms_contraint_level &&
         num_assigned < (size_t) max_var) {
    assert (num_assigned < (size_t) max_var);
    res = warmup_decide_assumptions ();
    if (!res && !propagate ()) {
      res = 20;
      marked_failed = false;
      break;
    }
  }
  if (conflict && !res)
    marked_failed = false, res = 20;

  const bool no_backtrack_notification = (level == 0);

  // now we do not need any notification and can simply propagate
  assert (res || propagated == trail.size ());
  assert (!private_steps);
  private_steps = true;

  LOG ("propagating beyond conflicts to warm-up walk");
  while (!res && num_assigned < (size_t) max_var - stats.unused) {
    assert (propagated == trail.size ());
    warmup_decide ();
    warmup_propagate_beyond_conflict ();
    LOG (lrat_chain, "during warmup with lrat chain:");
  }
  assert (res || num_assigned + stats.unused == (size_t) max_var);
#ifndef QUIET
  // constrains with empty levels break this
  // assert (res || stats.warmup.propagated - warmup_propagated ==
  // (int64_t)num_assigned);
  VERBOSE (3,
           "warming-up needed %" PRIu64 " propagations including %" PRIu64
           " decisions (with %" PRIu64 " dummy ones)",
           stats.warmup.propagated - warmup_propagated,
           stats.warmup.decision - decision,
           stats.warmup.dummydecision - dummydecision);
#endif

  // now we backtrack, notifying only if there was something to
  // notify.
  private_steps = no_backtrack_notification;
  if (!res)
    backtrack_without_updating_phases ();
  private_steps = false;
  STOP (warmup);
  require_mode (WALK);
  return res;
}

} // namespace CaDiCaL
