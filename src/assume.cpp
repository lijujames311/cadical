#include "internal.hpp"
#include "options.hpp"

namespace CaDiCaL {

// Failed literal handling as pioneered by MiniSAT.  This first function
// adds an assumption literal onto the assumption stack.

void Internal::assume (int lit) {
  if (level && !opts.ilb)
    backtrack ();
  else if (val (lit) < 0)
    backtrack (max (0, var (lit).level - 1));
  Flags &f = flags (lit);
  const unsigned char bit = bign (lit);
  if (f.assumed & bit) {
    LOG ("ignoring already assumed %d", lit);
    return;
  }
  LOG ("assume %d", lit);
  f.assumed |= bit;
  assumptions.push_back (lit);
  freeze (lit);
}

// for LRAT we actually need to implement recursive DFS
// for non-lrat use BFS. TODO: maybe derecursify to avoid stack overflow
//
void Internal::assume_analyze_literal (int lit) {
  assert (lit);
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
  LOG ("failed assumption %d", -lit);
  clause.push_back (lit);
}

void Internal::assume_analyze_reason (int lit, Clause *reason) {
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

    int failed_unit = 0;
    int failed_clashing = 0;
    int first_failed = 0;
    int failed_level = INT_MAX;
    int efailed = 0;

    for (auto &elit : external->assumptions) {
      int lit = external->e2i[abs (elit)];
      if (elit < 0)
        lit = -lit;
      if (val (lit) >= 0)
        continue;
      const Var &v = var (lit);
      if (!v.level) {
        failed_unit = lit;
        efailed = elit;
        break;
      }
      if (failed_clashing)
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
          int tmp = var (other).level;
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
      } else if (!first_failed || v.level < failed_level) {
        first_failed = lit;
        efailed = elit;
        failed_level = v.level;
      }
    }

    assert (clause.empty ());

    // Get the 'failed' assumption from one of the three cases.
    int failed;
    if (failed_unit)
      failed = failed_unit;
    else if (failed_clashing)
      failed = failed_clashing;
    else
      failed = first_failed;
    assert (failed);
    assert (efailed);

    // In any case mark literal 'failed' as failed assumption.
    {
      Flags &f = flags (failed);
      const unsigned bit = bign (failed);
      assert (!(f.failed & bit));
      f.failed |= bit;
    }

    // First case (1).
    if (failed_unit) {
      assert (failed == failed_unit);
      LOG ("root-level falsified assumption %d", failed);
      if (proof) {
        if (lrat) {
          unsigned eidx = (efailed > 0) + 2u * (unsigned) abs (efailed);
          assert ((size_t) eidx < external->ext_units.size ());
          const int64_t id = external->ext_units[eidx];
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
    if (failed_clashing) {
      assert (failed == failed_clashing);
      LOG ("clashing assumptions %d and %d", failed, -failed);
      Flags &f = flags (-failed);
      const unsigned bit = bign (-failed);
      assert (!(f.failed & bit));
      f.failed |= bit;
      if (proof) {
        vector<int> clash = {externalize (failed), externalize (-failed)};
        proof->add_assumption_clause (++clause_id, clash, lrat_chain);
        conclusion.push_back (clause_id);
      }
      goto DONE;
    }

    // Fall through to third case (3).
    LOG ("starting with assumption %d falsified on minimum decision level "
         "%d",
         first_failed, failed_level);

    assert (first_failed);
    assert (failed_level > 0);

    // The 'analyzed' stack serves as working stack for a BFS through the
    // implication graph until decisions, which are all assumptions, or
    // units are reached.  This is simpler than corresponding code in
    // 'analyze'.
    {
      LOG ("failed assumption %d", first_failed);
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
      lit *= -1;
      assert (lit != INT_MIN);
      flags (lit).seen = true;
      analyzed.push_back (lit);
    }
  }

  {
    // used for unsat_constraint lrat
    vector<vector<int64_t>> constraint_chains;
    vector<vector<int>> constraint_clauses;
    vector<int> sum_constraints;
    vector<int> econstraints;
    for (auto &elit : external->constraint) {
      int lit = external->e2i[abs (elit)];
      if (elit < 0)
        lit = -lit;
      if (!lit)
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
        const int lit = analyzed[next++];
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
          LOG ("failed assumption %d", lit);
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
      const int lit = clause[0];
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
        assert (lit != INT_MIN);
        assume_analyze_literal (lit);
        vector<int64_t> empty;
        vector<int> empty2;
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
        vector<int> eclause;
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
          vector<int> eclause;
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
            unsigned eidx = (elit > 0) + 2u * (unsigned) abs (elit);
            assert ((size_t) eidx < external->ext_units.size ());
            const int64_t id = external->ext_units[eidx];
            if (id) {
              lrat_chain.push_back (id);
            } else {
              int lit = external->e2i[abs (elit)];
              if (elit < 0)
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

bool Internal::failed (int lit) {
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

  Type operator() (const int &a) const {
    const int val = internal->val (a);
    const bool assigned = (val != 0);
    const Var &v = internal->var (a);
    uint64_t res = (assigned ? (unsigned) v.level : max_level);
    res <<= 32;
    res |= (assigned ? v.trail : abs (a));
    return res;
  }
};

struct sort_assumptions_smaller {
  Internal *internal;
  sort_assumptions_smaller (Internal *s) : internal (s) {}
  bool operator() (const int &a, const int &b) const {
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

  unsigned max_level = 0;
  // assumptions are sorted by level, with unset at the end
  for (auto lit : assumptions) {
    if (val (lit))
      max_level = var (lit).level;
    else
      break;
  }

  const unsigned size = min (level + 1u, max_level + 1);
  assert ((size_t) level == control.size () - 1);
  LOG (assumptions, "sorted assumptions");
  int target = 0;
  for (unsigned i = 1, j = 0; i < size;) {
    const Level &l = control[i];
    const int lit = l.decision;
    const int alit = assumptions[j];
    const int lev = i;
    target = lev;
    if (val (alit) > 0 &&
        var (alit).level < lev) { // we can ignore propagated assumptions
      LOG ("ILB skipping propagation %d", alit);
      ++j;
      continue;
    }
    if (!lit) { // skip fake decisions
      target = lev - 1;
      break;
    }
    ++i, ++j;
    assert (var (lit).level == lev);
    if (l.decision == alit) {
      continue;
    }
    target = lev - 1;
    LOG ("first different literal %d on the trail and %d from the "
         "assumptions",
         lit, alit);
    break;
  }
  if (opts.ilb == 1 &&
      (size_t) target > assumptions.size ()) // reusing only assumptions
    target = assumptions.size ();
  if (target < level)
    backtrack_without_updating_phases (target);
  LOG ("assumptions allow for reuse of trail up to level %d", level);
  if ((size_t) level > assumptions.size ())
    stats.assumptionsreused += assumptions.size ();
  else
    stats.assumptionsreused += level;
}

void Internal::push () {
  ctx_stack.emplace_back();
  switch_ctx(ctx_stack.size() - 1);
}

void Internal::pop () {
  if (level)
    backtrack ();
  assert (ctx_stack.size() > 1); // ensured in Solver::pop ()
  switch_ctx(ctx_stack.size() - 1);

  int activator_elit = ctx_stack[ctx_level].act_elit;//ctx_stack.back().act_elit;
  if (activator_elit) {
    popped_clauses += ctx_stack[ctx_level].stack_size;
    add_deactivator_unit_clause ();

    if (opts.ppassumptions <= 2) {
      // Find prev active context level and remove the propagating reason
    int prev_elit = 0;
    size_t prev_ctx_level = 0;
    for (auto idx = ctx_level - 1; idx > 0; idx--) {
      if (!ctx_stack[idx].is_empty_level()) {
        prev_elit = ctx_stack[idx].act_elit;
        prev_ctx_level = idx;
        break;
      }
    }
    if (prev_elit) {
      LOG ("reset activator chain clause of %d",prev_elit);
      ctx_stack[prev_ctx_level].reason = 0;
    }
    }
  }
  //pprecycle: "eagerness of additional recycling after pop (0: no 1: based on nof popped clauses 2: always)"


  // The always options is just "almost" always because arenaing is not playing well
  // when all clauses are removed in certain corner cases
  if (!unsat &&
     ((opts.pprecycle == 2 && popped_clauses > ctx_stack.size())||
      (opts.pprecycle == 1 && popped_clauses > 5000))) {
    
    if (propagated < trail.size ()) {
      if (!propagate ()) {
        LOG ("propagating units after elimination results in empty clause");
        learn_empty_clause ();
      } 
    }
    if (!unsat) {
      if (!internal->imports.empty()) internal->activating_all_new_imported_literals ();
      compact ();
    }
  }

  ctx_stack.resize(ctx_stack.size()-1);
  switch_ctx(ctx_stack.size() - 1);
}

bool Internal::init_ctx () {
  bool new_ctx_level_started = false;
  assert (ctx_level > 0);
  
  int activator_elit = ctx_stack[ctx_level].act_elit;
  int activator_ilit = 0;
  if (!activator_elit) {
    // Declare a new extension variable
    new_ctx_level_started = true;
    activator_ilit = get_new_extension_variable ();
    activator_elit =  i2e[activator_ilit]; // it is a fresh var, so i2e works
    freeze (activator_ilit);
    assert (activator_elit);
    Flags &f = flags(activator_ilit);
    assert (!f.activator);
    f.activator = true;
    LOG ("new activator variable is created for context level %ld: i%d (e%d)",ctx_level, activator_ilit, activator_elit);
    
    ctx_stack[ctx_level].act_elit = activator_elit;
    ctx_stack[ctx_level].activator = activator_ilit;
  }

  return new_ctx_level_started;
}

void Internal::add_activator_assumptions () {
  if (!ctx_stack.size())
    return;
  
  switch_ctx (ctx_stack.size() - 1);
  // The assumptions are added through external, so the proofs and checkers
  // also see them without any workaround, but it call internalize on the way
  if (opts.ppassumptions <= 2) {
    // Add the current activator literal as an assumption
    int activator_trigger_elit = 0;
    for (auto rit = ctx_stack.rbegin(); rit < ctx_stack.rend(); ++rit ) {
      if ((*rit).activator) {
        activator_trigger_elit = (*rit).act_elit;
        break;
      }
    }
    if (activator_trigger_elit) external->assume(activator_trigger_elit);
  } else {
    // Add all activator literals as an assumptions
    if (opts.ppassumptions == 3) {
      for (const auto cl : ctx_stack) {
        const int activator_elit = cl.act_elit;
        if (activator_elit) external->assume(activator_elit);
      }
    } else {
      assert (opts.ppassumptions == 4);
      // Assert all activators but in reverse order (top level is first)
      for (auto rit = ctx_stack.rbegin(); rit < ctx_stack.rend(); ++rit ) {
        if ((*rit).activator) {
          external->assume((*rit).act_elit);
        }
      }
    }
  } 
}

void Internal::add_deactivator_unit_clause () {
  if (!ctx_stack.size() || !ctx_level)
    return;

  const int unit_elit = -ctx_stack[ctx_level].act_elit;
  const int unit_ilit = -ctx_stack[ctx_level].activator;
  assert (abs (unit_ilit) <= max_var);
  if (!unit_elit || !unit_ilit)
    return;

  if (flags(unit_ilit).fixed())
    return;

  original.push_back (unit_ilit);  
  external->eclause.push_back(unit_elit);

  bool do_checking = (opts.check && (opts.checkwitness || opts.checkfailed));
  if (do_checking) {
    external->original.push_back(unit_elit);
    external->original.push_back(0);
  }

  LOG(original,"add new deactivator unit clause to root context level");

  const int64_t id = original_id < reserved_ids ? ++original_id : ++clause_id;

  if (proof) {
    assert (!original.size () || !external->eclause.empty ());
    proof->add_external_original_clause (id, false, external->eclause);
  }

  add_new_original_clause (id);
  original.clear ();
  external->eclause.clear();
}

void Internal::switch_ctx (int new_ctx_level) {
  assert (new_ctx_level >= 0 && (size_t)new_ctx_level < ctx_stack.size()); //ensured in Solver::switch
  if (ctx_level == (size_t)new_ctx_level) return;
  LOG ("switching context level from %ld to %d",ctx_level,new_ctx_level);
  ctx_level = new_ctx_level;
}

int Internal::max_ctx_level () const {
  return ctx_stack.size() - 1;
}

void Internal::add_activator_implication () {
  if (!ctx_stack.size())
    return;

  if (opts.ppassumptions > 2)
    return;

  assert (ctx_level > 0 &&  ctx_level < ctx_stack.size());
  assert (original.empty());
  assert (external->eclause.empty());

  bool do_checking = (opts.check && (opts.checkwitness || opts.checkfailed));
 
  const int act_elit = ctx_stack[ctx_level].act_elit;
  const int act_ilit = external->internalize(act_elit);

  if (ctx_level > 1 && !flags(act_ilit).fixed()) { //TODO: Check that it is fixed satisfied, not falsified!
    // Find the previous active context level
    int prev_elit = 0;
    size_t prev_ctx_level = 0;
    for (auto idx = ctx_level - 1; idx > 0; idx--) {
      if (!ctx_stack[idx].is_empty_level()) {
        prev_elit = ctx_stack[idx].act_elit;
        prev_ctx_level = idx;
        break;
      }
    }
    if (prev_elit) {
      assert (prev_ctx_level);

      
      const int prev_ilit = external->internalize(prev_elit);

      LOG("act elit: %d act ilit: %d internalize(act_elit): %d",act_elit,ctx_stack[ctx_level].activator,act_ilit);
      LOG("prev elit: %d prev ilit: %d internalize(prev_elit): %d",prev_elit,ctx_stack[prev_ctx_level].activator,external->internalize(prev_elit));

      assert (act_ilit); 
      assert (!flags(act_ilit).fixed());
        // The current level is not the first active one, we need to add the
        // implication current activator -> prev activator
        // If prev is already fixed, we still need to add this clause, so that
        // act_ilit can become fixed as well.
        
        original.push_back(prev_ilit);
        original.push_back(-act_ilit);

        external->eclause.push_back(prev_elit);
        external->eclause.push_back(-act_elit);

        if (do_checking) {
          external->original.push_back(prev_elit);
          external->original.push_back(-act_elit);
          external->original.push_back(0);
          // if (lrat) external->ext_flags[abs (elit)] = true;
        }

        LOG(original,"add new activator trigger binary clause to root context level");

        const int64_t id = original_id < reserved_ids ? ++original_id : ++clause_id;
        if (proof) {
          assert (!original.size () || !external->eclause.empty ());
          proof->add_external_original_clause (id, false, external->eclause);
        }

        add_new_original_clause (id);
        

        if (newest_clause) {
          LOG (newest_clause, "new activator reason clause %p", (void *) newest_clause);
          assert (newest_clause->id == id);
          ctx_stack[prev_ctx_level].reason = newest_clause;
          ctx_stack[ctx_level].stack_size++;
        } // else: The clause got simplified, which means the implication became a unit
          // clause that will take care of itself, so nothing left to add as reason

        original.clear ();
        external->eclause.clear();
    
    }
  }

  if (ctx_stack.size() > 2 && ctx_level < ctx_stack.size() - 1) {
    int next_elit = 0;
    size_t next_ctx_level = 0;
    for (auto idx = ctx_level + 1; idx < ctx_stack.size(); idx++) {
      if (!ctx_stack[idx].is_empty_level()) {
        next_elit = ctx_stack[idx].act_elit;
        next_ctx_level = idx;
        break;
      }
    }
    if (next_elit) {
      assert(next_ctx_level);

      // const int act_elit = ctx_stack[ctx_level].act_elit;
      // const int act_ilit = external->internalize(act_elit);
      const int next_ilit = external->internalize(next_elit);

      LOG("act elit: %d act ilit: %d internalize(act_elit): %d",act_elit,ctx_stack[ctx_level].activator,act_ilit);
      LOG("next elit: %d next ilit: %d internalize(next_elit): %d",next_elit,next_ilit,external->internalize(next_elit));

      assert (act_ilit); 
      
      
      // The current level is not the first active one, we need to add the
      // implication next activator -> current activator
      
      original.push_back(-next_ilit);
      original.push_back(act_ilit);

      external->eclause.push_back(-next_elit);
      external->eclause.push_back(act_elit);

      if (do_checking) {
        external->original.push_back(-next_elit);
        external->original.push_back(act_elit);
        external->original.push_back(0);
        // if (lrat) external->ext_flags[abs (elit)] = true;
      }

      LOG(original,"add new activator trigger binary clause to root context level");

      const int64_t id = original_id < reserved_ids ? ++original_id : ++clause_id;
      if (proof) {
        assert (!original.size () || !external->eclause.empty ());
        proof->add_external_original_clause (id, false, external->eclause);
      }

      add_new_original_clause (id);
      

      if (newest_clause) {
        LOG (newest_clause, "new activator reason clause %p", (void *) newest_clause);
        assert (newest_clause->id == id);
        ctx_stack[ctx_level].reason = newest_clause;
        ctx_stack[next_ctx_level].stack_size++;
      } // else: The clause got simplified, which means the implication became a unit
        // clause that will take care of itself, so nothing left to add as reason

      original.clear ();
      external->eclause.clear(); 
    }
  }

  assert (ctx_level > 0 &&  ctx_level < ctx_stack.size());
  assert (original.empty());
  assert (external->eclause.empty());
}

} // namespace CaDiCaL
