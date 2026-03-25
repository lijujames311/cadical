#include "flags.hpp"
#include "internal.hpp"
#include "literals.hpp"
#include "util.hpp"

#include <cstdint>

namespace CaDiCaL {

External::External (Internal *i)
    : internal (i), max_var (0), vsize (0), extended (false),
      concluded (false), terminator (0), learner (0), fixed_listener (0),
      propagator (0), solution (0), vars (max_var) {
  assert (internal);
  assert (!internal->external);
  internal->external = this;
}

External::~External () {
  if (solution)
    delete[] solution;
}

void External::enlarge (ELit new_max_var) {
  assert (!extended);
  assert (!new_max_var.is_negated());
  size_t new_vsize = vsize ? 2 * vsize : 1 + (size_t) new_max_var.var ();
  while (new_vsize <= (size_t) new_max_var.var ())
    new_vsize *= 2;
  LOG ("enlarge external size from %zd to new size %zd", vsize, new_vsize);
  vsize = new_vsize;
}

Lit External::declare_var (ELit new_var, bool extension) {
  assert (new_var != INVALID_ELIT);
  assert (new_var.is_positive());
  Lit ilit = internal_lit (new_var);
  if (ilit == INVALID_LIT) {
    if (!internal->opts.varkeepname)
      ilit = Lit (internal->max_var+1);
    else {
      ilit = Lit (new_var.signed_representation ());
      if (internal->to_external_var (ilit) != INVALID_ELIT) {
        LOG ("the slot is already used by %s, giving the next available name", LOGLIT (internal->to_external_var (ilit)));
        ilit = Lit (internal->max_var+1);
      }
    }
    LOG ("new mapping external %s to internal %s", LOGLIT (new_var), LOGLIT (ilit));
    e2i[new_var] = ilit;
    internal->to_external_var (ilit) = new_var;
    internal->declare_variable (ilit);
    assert (Lit (internal->max_var) >= ilit);
  }

  (void)extension;
  return e2i[new_var];
}

void External::resize (ELit new_max_lit) {
  ELit::base_type new_max_var = new_max_lit.var ();
  assert (max_var < new_max_var);
  //internal->reserve_vars (new_max_var);
  //reserve_at_least (ext_units, 2 * new_max_var + 2);
  if (!max_var) {
    assert (e2i.empty ());
    ELit elit (0);
    is_extension_var(elit) = false;
    external_marked(elit) = false;
    internal->i2e[INVALID_LIT] = elit;
  }
  int new_vars = new_max_var - max_var;
  max_var = new_max_var;
  internal->stats.variables_original += new_vars;
}

void External::init (ELit new_max_lit, bool extension) {
  ELit::base_type new_max_var = new_max_lit.var ();
  assert (!extended);
  LOG ("%s external variables from %s", LOGLIT (new_max_lit), LOGLIT (ELit (max_var)));
  if (new_max_var <= max_var) {
    declare_var (new_max_lit.labs (), extension);
    return;
  }
  int new_vars = new_max_var - max_var;
  LOG ("initialized %d external variables", new_vars);
  resize (new_max_lit);

  //declare_var (new_max_lit, extension);
  if (extension)
    internal->stats.variables_extension += new_vars;
  else
    internal->stats.variables_original += new_vars;
  if (internal->opts.checkfrozen)
    if (new_max_var >= (int64_t) moltentab.size ())
      moltentab.resize (1 + (size_t) new_max_var, false);
}

/*------------------------------------------------------------------------*/

void External::reset_assumptions () {
  assumptions.clear ();
  internal->reset_assumptions ();
}

void External::reset_concluded () {
  concluded = false;
  internal->reset_concluded ();
}

void External::reset_constraint () {
  constraint.clear ();
  internal->reset_constraint ();
}

void External::reset_extended () {
  if (!extended)
    return;
  LOG ("reset extended");
  extended = false;
}

void External::reset_limits () { internal->reset_limits (); }

/*------------------------------------------------------------------------*/

// when extension is true, elit should be a fresh variable and
// we can set a flag that it is an extension variable.
// This is then used in the API contracts, that extension variables are
// never part of the input
Lit External::internalize (ELit elit, bool extension) {
  Lit ilit;
  if (elit != INVALID_ELIT) {
    assert (elit != OTHER_INVALID_ELIT);
    const ELit eidx = elit.labs ();
    if (extension && eidx <= ELit (max_var))
      FATAL ("can not add a definition for an already used variable %" EVAR,
        eidx.signed_representation());
    if (eidx > ELit (max_var)) {
      init (eidx, extension);
    }
    if (extension) {
      is_extension_var (eidx) = true;
    }
    ilit = e2i[eidx];
    if (ilit == INVALID_LIT)
      ilit = declare_var (eidx, false);
    if (elit.is_negated ())
      ilit = -ilit;
    assert (ilit != INVALID_LIT);
    if (ilit == INVALID_LIT) {
      assert (internal->max_var < INT_MAX);
      ilit = Lit (internal->max_var + 1u);
      internal->reserve_vars (ilit.var ());
      e2i[eidx] = ilit;
      LOG ("mapping external %s to internal %s", LOGLIT(eidx), LOGLIT(ilit));
      e2i[eidx] = ilit;
      assert (internal->to_external_var(ilit) == eidx);
      assert (e2i[eidx] == ilit);
      if (elit.is_negated())
        ilit = -ilit;
    }
    if (internal->opts.checkfrozen) {
      assert (eidx.var () < (int64_t) moltentab.size ());
      if (moltentab[eidx.var ()])
        FATAL ("can not reuse molten literal %" EVAR, eidx.signed_representation());
    }
    Flags &f = internal->flags (ilit);
    if (f.status == Flags::UNUSED)
      internal->declare_variable (ilit);
    else if (f.status != Flags::DECLARED && f.status != Flags::ACTIVE && f.status != Flags::FIXED) {
      internal->reactivate (ilit);
    }
    if (!marked (tainted, elit) && marked (witness, -elit)) {
      assert (!internal->opts.checkfrozen);
      LOG ("marking tainted %s", LOGLIT(elit));
      mark (tainted, elit);
    }
  } else
    ilit = INVALID_LIT;
  return ilit;
}

void External::add (ELit elit) {
  assert (elit != OTHER_INVALID_ELIT);

  if (elit != INVALID_ELIT)
    REQUIRE (is_valid_input (elit),
             "extension variable '%" EVAR "' defined by the solver internally "
             "(all user variables have to be declared explicitly "
	     "if 'factor' is enabled)", // TODO only reason?
             elit.signed_representation());
  reset_extended ();

  bool forgettable = false;

  if (internal->opts.check &&
      (internal->opts.checkwitness || internal->opts.checkfailed)) {

    forgettable =
        internal->from_propagator && internal->ext_clause_forgettable;

    // Forgettable clauses (coming from the external propagator) are not
    // saved into the external 'original' stack. They are stored separately
    // in external 'forgettable_original', from where they are deleted when
    // the corresponding clause is deleted (actually deleted, not just
    // marked as garbage).
    if (!forgettable)
      original.push_back (elit);
  }

  const Lit ilit = internalize (elit);
  assert ((elit == INVALID_ELIT) == (ilit == INVALID_LIT));

  // The external literals of the new clause must be saved for later
  // when the proof is printed during add_original_lit (0)
  if (elit != INVALID_ELIT && (internal->proof || forgettable)) {
    eclause.push_back (elit);
    if (internal->lrat) {
      // actually find unit of -elit (flips elit < 0)
      unsigned eidx = (-elit).vlit ();
      const int64_t id = ext_units[eidx];
      bool added = external_marked (elit);
      LOG ("%s not a unit: %" PRId64, LOGLIT (elit), id);
      if (id && !added) {
        external_marked (elit) = true;
        internal->lrat_chain.push_back (id);
      }
    }
  }

  if (elit == INVALID_ELIT && internal->proof && internal->lrat) {
    for (const auto &elit : eclause) {
      external_marked (elit) = false;
    }
  }

  if (elit != INVALID_ELIT)
    LOG ("adding external %s as internal %s", LOGLIT(elit), LOGLIT(ilit));
  if (internal->external_prop)
    internal->activating_all_new_imported_literals ();
  internal->add_original_lit (ilit);

  // Clean-up saved external literals once proof line is printed
  if (elit == INVALID_ELIT && (internal->proof || forgettable))
    eclause.clear ();
}

void External::assume (ELit elit) {
  assert (elit.var ());
  reset_extended ();
  if (internal->proof)
    internal->proof->add_assumption (elit);
  assumptions.push_back (elit);
  const Lit ilit = internalize (elit);
  assert (ilit != INVALID_LIT);
  LOG ("assuming external %s as internal %s", LOGLIT(elit), LOGLIT(ilit));
  internal->assume (ilit);
}

bool External::flip (ELit elit) {
  assert (elit != INVALID_ELIT);
  assert (elit != OTHER_INVALID_ELIT);
  assert (!propagator);

  int eidx = elit.var ();
  if (eidx > max_var)
    return false;
  if (marked (witness, elit))
    return false;
  Lit ilit = e2i[elit.labs ()];
  if (ilit == INVALID_LIT)
    return false;
  bool res = internal->flip (ilit);
  if (res && extended)
    reset_extended ();
  return res;
}

bool External::flippable (ELit elit) {
  assert (elit != INVALID_ELIT);
  assert (elit != OTHER_INVALID_ELIT);
  assert (!propagator);

  int eidx = elit.var ();
  if (eidx > max_var)
    return false;
  if (marked (witness, elit))
    return false;
  Lit ilit = e2i[elit.labs ()];
  if (ilit == INVALID_LIT)
    return false;
  return internal->flippable (ilit);
}

bool External::failed (ELit elit) {
  assert (elit != INVALID_ELIT);
  assert (elit != OTHER_INVALID_ELIT);
  int eidx = elit.var ();
  if (eidx > max_var)
    return 0;
  Lit ilit = e2i[elit.labs ()];
  if (ilit == INVALID_LIT)
    return 0;
  if (elit.is_negated())
    ilit = -ilit;
  return internal->failed (ilit);
}

void External::constrain (ELit elit) {
  if (constraint.size () && constraint.back () == INVALID_ELIT) {
    LOG (constraint, "replacing previous constraint");
    reset_constraint ();
  }
  assert (elit != OTHER_INVALID_ELIT);
  reset_extended ();
  const Lit ilit = internalize (elit);
  assert ((elit != INVALID_ELIT) == (ilit != INVALID_LIT));
  if (elit != INVALID_ELIT)
    LOG ("adding external %s as internal %s to constraint", LOGLIT(elit), LOGLIT(ilit));
  else if (elit == INVALID_ELIT && internal->proof) {
    internal->proof->add_constraint (constraint);
  }
  constraint.push_back (elit);
  internal->constrain (ilit);
}

bool External::failed_constraint () {
  return internal->failed_constraint ();
}

void External::phase (ELit elit) {
  assert (elit != INVALID_ELIT);
  assert (elit != OTHER_INVALID_ELIT);
  // this test is a bit stupid, it is triggereing an assertion, but we we could
  // simply add thos to the other if...
  if (elit.var () > max_var) {
    reset_extended ();
  }
  const Lit ilit = internalize (elit);
  if (!internal->imports.empty()) {
    if (extended)
      reset_extended ();
    internal->activating_all_new_imported_literals ();
  }
  internal->phase (ilit);
}

void External::unphase (ELit elit) {
  assert (elit != INVALID_ELIT);
  assert (elit != OTHER_INVALID_ELIT);
  int eidx = elit.var ();
  if (eidx > max_var) {
  UNUSED:
    LOG ("resetting forced phase of unused external %s ignored", LOGLIT(elit));
    return;
  }
  Lit ilit = e2i[elit.labs ()];
  if (ilit == INVALID_LIT)
    goto UNUSED;
  if (elit.is_negated())
    ilit = -ilit;
  internal->unphase (ilit);
}

/*------------------------------------------------------------------------*/

// External propagation related functions
//
// Note that when an already assigned variable is added as observed, the
// solver will backtrack to undo this assignment.
//
void External::add_observed_var (ELit elit) {
  assert (propagator); // REQ is in Solver::add_observed_var
  assert (elit != INVALID_ELIT);
  assert (elit != OTHER_INVALID_ELIT);
  reset_extended (); // tainting!

  int eidx = elit.var ();

  REQUIRE (eidx > max_var ||
               (!marked (witness, elit) && !marked (witness, -elit)),
           "Only clean variables are allowed to be observed.");
  // if (eidx <= max_var &&
  //     (marked (witness, elit) || marked (witness, -elit))) {
  //   LOG ("Error, only clean variables are allowed to become observed.");
  //   assert (false);

  //   // TODO: here needs to come the taint and restore of the newly
  //   // observed variable. Restore_clauses must be called before continue.
  //   // LOG ("marking tainted %d", elit);
  //   // mark (tainted, elit);
  //   // mark (tainted, -elit);
  //   // restore_clauses ...
  // }

  if (eidx >= (int64_t) is_observed.size ())
    is_observed.resize (1 + (size_t) eidx, false);

  if (is_observed[eidx])
    return;

  LOG ("marking %s as externally watched", LOGLIT(elit));

  Lit ilit = internalize (elit);
  // Will do the necessary internalization
  freeze (elit);
  is_observed[eidx] = true;

  // internal add-observed-var backtracks to a lower decision level to
  // unassign the variable in case it was already assigned previously (but
  // not on the current level)
  internal->add_observed_var (ilit);

  if (propagator->is_lazy)
    return;

  // In case this variable was already assigned (e.g. via unit clause) and
  // got compacted to map to another (not observed) variable, it can not be
  // unnasigned so it must be notified explicitly now. (-> Can lead to
  // repeated fixed assignment notifications, in case it was unobserved and
  // observed again. But a repeated notification is less error-prone than
  // never notifying an assignment.)
  const int tmp = fixed (elit);
  if (!tmp)
    return;
  ELit unit = tmp < 0 ? -elit : elit;

  LOG ("notify propagator about fixed assignment upon observe for %s",
       LOGLIT(unit));

  // internal add-observed-var had to backtrack to root-level already
  assert (!internal->level);

  std::vector<ELit::base_type> assigned = {unit.signed_representation()};
  propagator->notify_assignment (assigned);
}

void External::remove_observed_var (ELit elit) {
  assert (propagator); // REQ is in Solver::remove_observed_var

  int eidx = elit.var ();

  if (eidx > max_var) // Ignore call if variable does not exist
    return;

  // Ignore call if variable is not observed
  if ((size_t) eidx >= is_observed.size ())
    return;
  if (is_observed[eidx]) {
    // Follow opposite order of add_observed_var, first remove internal
    // is_observed
    Lit ilit = e2i[elit.labs ()]; // internalize (elit);
    internal->remove_observed_var (ilit);

    is_observed[eidx] = false;
    melt (elit);
    LOG ("unmarking %s as externally watched", LOGLIT(elit));
  }
}

void External::reset_observed_vars () {
  // Shouldn't be called if there is no connected propagator
  assert (propagator); // REQ is in Solver::reset_observed_vars
  reset_extended ();

  internal->notified = 0;
  LOG ("reset notified counter to 0");

  if (!is_observed.size ())
    return;

  for (auto elit : vars) {
    int eidx = elit.var ();
    assert (eidx <= max_var);
    if ((size_t) eidx >= is_observed.size ())
      break;
    if (is_observed[eidx]) {
      Lit ilit = internalize (elit);
      internal->remove_observed_var (ilit);
      LOG ("unmarking %s as externally watched", LOGLIT(elit));
      is_observed[eidx] = false;
      melt (elit);
    }
  }
}

bool External::observed (ELit elit) {
  assert (elit != INVALID_ELIT);
  assert (elit != OTHER_INVALID_ELIT);
  int eidx = elit.var ();
  if (eidx > max_var)
    return false;
  if (eidx >= (int) is_observed.size ())
    return false;

  return is_observed[eidx];
}

bool External::is_witness (ELit elit) {
  assert (elit != INVALID_ELIT);
  assert (elit != OTHER_INVALID_ELIT);
  int eidx = elit.var ();
  if (eidx > max_var)
    return false;
  return (marked (witness, elit) || marked (witness, -elit));
}

bool External::is_decision (ELit elit) {
  assert (elit != INVALID_ELIT);
  assert (elit != OTHER_INVALID_ELIT);
  int eidx = elit.var ();
  if (eidx > max_var)
    return false;

  Lit ilit = internalize (elit);
  return internal->is_decision (ilit);
}

void External::force_backtrack (int new_level) {
  assert (propagator); // REQ is is in Solver::force_backtrack

  LOG ("force backtrack to level %d", new_level);
  internal->force_backtrack (new_level);
}

/*------------------------------------------------------------------------*/

int External::propagate_assumptions () {
  int res = internal->propagate_assumptions ();
  if (res == 10 && !extended)
    extend (); // Call solution reconstruction
  check_solve_result (res);
  reset_limits ();
  return res;
}

void External::implied (std::vector<int> &trailed) {
  std::vector<Lit> ilit_implicants;
  internal->implied (ilit_implicants);

  // Those implied literals must be filtered out that are witnesses
  // on the reconstruction stack -> no inplace externalize is possible.
  // (Internal does not see these marks, so no earlier filter is
  // possible.)

  trailed.clear ();

  for (const auto &ilit : ilit_implicants) {
    assert (ilit != INVALID_LIT);
    const ELit elit = internal->externalize (ilit);
    const bool is_extension = is_extension_var (elit);
    if (!marked (tainted, elit) && !is_extension) {
      trailed.push_back (elit.signed_representation());
    }
  }
}

void External::conclude_unknown () {
  if (!internal->proof || concluded)
    return;
  concluded = true;

  vector<int> trail;
  implied (trail);
  internal->proof->conclude_unknown (trail);
}

/*------------------------------------------------------------------------*/

// Internal checker if 'solve' claims the formula to be satisfiable.

void External::check_satisfiable () {
  LOG ("checking satisfiable");
  if (!extended)
    extend ();
  if (internal->opts.checkwitness)
    check_assignment (&External::ival);
  if (internal->opts.checkassumptions && !assumptions.empty ())
    check_assumptions_satisfied ();
  if (internal->opts.checkconstraint && !constraint.empty ())
    check_constraint_satisfied ();
}

// Internal checker if 'solve' claims formula to be unsatisfiable.

void External::check_unsatisfiable () {
  LOG ("checking unsatisfiable");
  if (!internal->opts.checkfailed)
    return;
  if (!assumptions.empty () || !constraint.empty ())
    check_failing ();
}

// Check result of 'solve' to be correct.

void External::check_solve_result (int res) {
  if (!internal->opts.check)
    return;
  if (res == 10)
    check_satisfiable ();
  if (res == 20)
    check_unsatisfiable ();
}

// Prepare checking that completely molten literals are not used as argument
// of 'add' or 'assume', which is invalid under freezing semantics.  This
// case would be caught by our 'restore' implementation so is only needed
// for checking the deprecated 'freeze' semantics.

void External::update_molten_literals () {
  if (!internal->opts.checkfrozen)
    return;
  assert ((size_t) max_var + 1 == moltentab.size ());
#ifdef LOGGING
  int registered = 0, molten = 0;
#endif
  for (auto lit : vars) {
    if (moltentab[lit.var ()]) {
      LOG ("skipping already molten literal %s", LOGLIT(lit));
#ifdef LOGGING
      molten++;
#endif
    } else if (frozen (lit))
      LOG ("skipping currently frozen literal %s", LOGLIT(lit));
    else {
      LOG ("new molten literal %s", LOGLIT(lit));
      moltentab[lit.var ()] = true;
#ifdef LOGGING
      registered++;
      molten++;
#endif
    }
  }
  LOG ("registered %d new molten literals", registered);
  LOG ("reached in total %d molten literals", molten);
}

int External::solve (bool preprocess_only) {
  reset_extended ();
  update_molten_literals ();
  int res = internal->solve (preprocess_only);
  check_solve_result (res);
  reset_limits ();
  return res;
}

void External::terminate () { internal->terminate (); }

ELit External::lookahead () {
  reset_extended ();
  update_molten_literals ();
  Lit ilit = internal->lookahead ();
  const ELit elit =
      (ilit != INVALID_LIT && ilit != OTHER_INVALID_LIT) ? internal->externalize (ilit) : INVALID_ELIT;
  LOG ("lookahead internal %s external %s", LOGLIT(ilit), LOGLIT(elit));
  return elit;
}

CaDiCaL::CubesWithStatus External::generate_cubes (int depth,
                                                   int min_depth = 0) {
  reset_extended ();
  update_molten_literals ();
  reset_limits ();
  auto cubes = internal->generate_cubes (depth, min_depth);
  CaDiCaL::CubesWithStatus external_cubes;
  for (const auto & cube : cubes.cubes) {
    std::vector<int> ecube;
    for (auto ilit : cube) {
      const ELit elit = ilit != INVALID_LIT ? internal->externalize (ilit) : INVALID_ELIT;
      LOG ("lookahead internal %s external %s", LOGLIT(ilit), LOGLIT(elit));
      ecube.push_back(elit.signed_representation());
    }
    cubes.cubes.push_back(std::move (cube));
  }
  external_cubes.status = cubes.status;
  return external_cubes;
}

/*------------------------------------------------------------------------*/

void External::freeze (ELit elit) {
  reset_extended ();
  Lit ilit = internalize (elit);
  unsigned eidx = vidx (elit);
  if (eidx >= frozentab.size ())
    frozentab.resize (eidx + 1, 0);
  unsigned &ref = frozentab[eidx];
  if (ref < UINT_MAX) {
    ref++;
    LOG ("external variable %s frozen once and now frozen %u times", LOGLIT(elit),
         ref);
  } else
    LOG ("external variable %s frozen but remains frozen forever", LOGLIT(elit));
  internal->freeze (ilit);
}

void External::melt (ELit elit) {
  reset_extended ();
  Lit ilit = internalize (elit);
  unsigned eidx = vidx (elit);
  assert (eidx < frozentab.size ());
  unsigned &ref = frozentab[eidx];
  assert (ref > 0);
  if (ref < UINT_MAX) {
    if (!--ref) {
      if (observed (elit)) {
        ref++;
        LOG ("external variable %s is observed, can not be completely "
             "molten",
             LOGLIT(elit));
      } else
        LOG ("external variable %s melted once and now completely melted",
             LOGLIT(elit));
    } else
      LOG ("external variable %s melted once but remains frozen %u times",
           LOGLIT(elit), ref);
  } else
    LOG ("external variable %s melted but remains frozen forever", LOGLIT(elit));
  internal->melt (ilit);
}

/*------------------------------------------------------------------------*/

void External::check_assignment (ELit (External::*a) (ELit) const) {

  // First check all assigned and consistent.
  //
  for (auto idx : vars) {
    if ((this->*a) (idx) == INVALID_ELIT)
      FATAL ("unassigned variable: %" EVAR, idx.signed_representation());
    ELit value_idx = (this->*a) (idx);
    ELit value_neg_idx = (this->*a) (-idx);
    if (value_idx == idx)
      assert (value_neg_idx == idx);
    else {
      assert (value_idx == -idx);
      assert (value_neg_idx == -idx);
    }
    if (value_idx != value_neg_idx)
      FATAL ("inconsistently assigned literals %" EVAR " and %" EVAR "", (idx).signed_representation(), (-idx).signed_representation());
  }

  // Then check that all (saved) original clauses are satisfied.
  //
  bool satisfied = false;
  const auto end = original.end ();
  auto start = original.begin (), i = start;
#ifndef QUIET
  int64_t count = 0;
#endif
  for (; i != end; i++) {
    ELit lit = *i;
    if (lit == INVALID_ELIT) {
      if (!satisfied) {
        fatal_message_start ();
        fputs ("unsatisfied clause:\n", stderr);
        for (auto j = start; j != i; j++)
          fprintf (stderr, "%" EVAR " ", (*j).signed_representation());
        fputc ('0', stderr);
        fatal_message_end ();
      }
      satisfied = false;
      start = i + 1;
#ifndef QUIET
      count++;
#endif
    } else if (!satisfied && (this->*a) (lit) == lit)
      satisfied = true;
  }

  bool presence_flag;
  // Check those forgettable external clauses that are still present, but
  // only if the external propagator is still connected (otherwise solution
  // reconstruction is allowed to touch the previously observed variables so
  // there is no guarantee that the final model will satisfy these clauses.)
  for (const auto &forgettables : forgettable_original) {
    if (!propagator)
      break;
    presence_flag = true;
    satisfied = false;
#ifndef QUIET
    count++;
#endif
    std::vector<int> literals;
    for (const auto lit : forgettables.second) {
      if (presence_flag) {
        // First integer is a Boolean flag, not a literal
        if (lit == INVALID_ELIT) {
          // Deleted clauses can be ignored, they count as satisfied
          satisfied = true;
          break;
        }
        presence_flag = false;
        continue;
      }

      if ((this->*a) (lit) == lit) {
        satisfied = true;
        break;
      }
    }

    if (!satisfied) {
      fatal_message_start ();
      fputs ("unsatisfied external forgettable clause:\n", stderr);
      for (size_t j = 1; j < forgettables.second.size (); j++)
        fprintf (stderr, "%" EVAR " ", (forgettables.second[j]).signed_representation());
      fputc ('0', stderr);
      fatal_message_end ();
    }
  }
#ifndef QUIET
  VERBOSE (1, "satisfying assignment checked on %" PRId64 " clauses",
           count);
#endif
}

/*------------------------------------------------------------------------*/

void External::check_assumptions_satisfied () {
  for (const auto &lit : assumptions) {
    // Not 'signed char' !!!!
    const ELit tmp = ival (lit);
    if (tmp != lit)
      FATAL ("assumption %" EVAR " falsified", (lit).signed_representation());
    assert (tmp != ELit (0)); // checks if assigned
  }
  VERBOSE (1, "checked that %zd assumptions are satisfied",
           assumptions.size ());
}

void External::check_constraint_satisfied () {
  for (const auto lit : constraint) {
    if (ival (lit) == lit) {
      VERBOSE (1, "checked that constraint is satisfied");
      return;
    }
  }
  FATAL ("constraint not satisfied");
}

void External::check_failing () {
  Solver *checker = new Solver ();
  DeferDeletePtr<Solver> delete_checker (checker);
  checker->prefix ("checker ");
#ifdef LOGGING
  if (internal->opts.log)
    checker->set ("log", true);
#endif
  checker->set ("factorcheck", false);

  for (const auto lit : assumptions) {
    if (!failed (lit))
      continue;
    LOG ("checking failed literal %s in core", LOGLIT(lit));
    checker->add (lit.signed_representation());
    checker->add (0);
  }
  if (failed_constraint ()) {
    LOG (constraint, "checking failed constraint");
    for (const auto lit : constraint)
      checker->add (lit.signed_representation());
  } else if (constraint.size ())
    LOG (constraint, "constraint satisfied and ignored");

  // Add original clauses as last step, failing () and failed_constraint ()
  // might add more external clauses (due to lazy explanation)
  for (const auto lit : original)
    checker->add (lit.signed_representation());

  // Add every forgettable external clauses
  for (const auto &forgettables : forgettable_original) {
    bool presence_flag = true;
    for (const auto lit : forgettables.second) {
      if (presence_flag) {
        // First integer is a Boolean flag, not a literal, ignore it here
        presence_flag = false;
        continue;
      }
      checker->add (lit.signed_representation());
    }
    checker->add (0);
  }

  int res = checker->solve ();
  if (res != 20)
    FATAL ("failed assumptions do not form a core");
  delete_checker.free ();
  VERBOSE (1, "checked that %zd failing assumptions form a core",
           assumptions.size ());
}

/*------------------------------------------------------------------------*/

// Traversal of unit clauses is implemented here.

// In principle we want to traverse the clauses of the simplified formula
// only, particularly eliminated variables should be completely removed.
// This poses the question what to do with unit clauses.  Should they be
// considered part of the simplified formula or of the witness to construct
// solutions for the original formula?  Ideally they should be considered
// to be part of the witness only, i.e., as they have been simplified away.

// Therefore we distinguish frozen and non-frozen units during clause
// traversal.  Frozen units are treated as unit clauses while non-frozen
// units are treated as if they were already eliminated and put on the
// extension stack as witness clauses.

// Furthermore, eliminating units during 'compact' could be interpreted as
// variable elimination, i.e., just add the resolvents (remove falsified
// literals), then drop the clauses with the unit, and push the unit on the
// extension stack.  This is of course only OK if the user did not freeze
// that variable (even implicitly during assumptions).

// Thanks go to Fahiem Bacchus for asking why there is a necessity to
// distinguish these two cases (frozen and non-frozen units).  The answer is
// that it is not strictly necessary, and this distinction could be avoided
// by always treating units as remaining unit clauses, thus only using the
// first of the two following functions and dropping the 'if (!frozen (idx))
// continue;' check in it.  This has however the down-side that those units
// are still in the simplified formula and only as units.  I would not
// consider such a formula as really being 'simplified'. On the other hand
// if the user explicitly freezes a literal, then it should continue to be
// in the simplified formula during traversal.  So also only using the
// second function is not ideal.

// There is however a catch where this solution breaks down (in the sense of
// producing less optimal results - that is keeping units in the formula
// which better would be witness clauses).  The problem is with compact
// preprocessing which removes eliminated but also fixed internal variables.
// One internal unit (fixed) variable is kept and all the other external
// literals which became unit are mapped to that internal literal (negated
// or positively).  Compact is called non-deterministically from the point
// of the user and thus there is no control on when this happens.  If
// compact happens those external units are mapped to a single internal
// literal now and then all share the same 'frozen' counter.   So if the
// user freezes one of them all in essence get frozen, which in turn then
// makes a difference in terms of traversing such a unit as unit clause or
// as unit witness.

bool External::traverse_all_frozen_units_as_clauses (ClauseIterator &it) {
  if (internal->unsat)
    return true;

  vector<int> clause;

  for (auto idx : vars) {
    if (!frozen (idx))
      continue;
    const int tmp = fixed (idx);
    if (!tmp)
      continue;
    ELit unit = tmp < 0 ? -idx : idx;
    clause.push_back (unit.signed_representation ());
    if (!it.clause (clause))
      return false;
    clause.clear ();
  }

  return true;
}

bool External::traverse_all_non_frozen_units_as_witnesses (
    WitnessIterator &it) {
  if (internal->unsat)
    return true;

  vector<int> clause_and_witness;
  for (auto idx : vars) {
    if (frozen (idx))
      continue;
    const int tmp = fixed (idx);
    if (!tmp)
      continue;
    ELit unit = tmp < 0 ? -idx : idx;
    const Lit ilit = (tmp < 0 ? -1 : 1) * e2i[idx];
    // heurstically add + max_var to the id to avoid reusing ids
    const int64_t id = internal->lrat ? internal->unit_id (ilit) : 1;
    assert (id);
    clause_and_witness.push_back (unit.signed_representation());
    if (!it.witness (clause_and_witness, clause_and_witness, id + max_var))
      return false;
    clause_and_witness.clear ();
  }

  return true;
}

/*------------------------------------------------------------------------*/

void External::copy_flags (External &other) const {
  const vector<Flags> &this_ftab = internal->ftab;
  vector<Flags> &other_ftab = other.internal->ftab;
  const unsigned limit = min (max_var, other.max_var);
  for (unsigned eidx = 1; eidx <= limit; eidx++) {
    const ELit elit = ELit (eidx);
    const Lit this_ilit = internal_lit (elit);
    if (this_ilit == INVALID_LIT)
      continue;
    const Lit other_ilit = other.e2i[elit];
    if (other_ilit == INVALID_LIT)
      continue;
    if (!internal->active (this_ilit))
      continue;
    if (!other.internal->active (other_ilit))
      continue;
    assert (this_ilit != INVALID_LIT);
    assert (other_ilit != INVALID_LIT);
    const Flags &this_flags = this_ftab[this_ilit.var ()];
    Flags &other_flags = other_ftab[other_ilit. var ()];
    this_flags.copy (other_flags);
  }
  internal->external->ervars = other.ervars;
}

/*------------------------------------------------------------------------*/
void External::export_learned_empty_clause () {
  assert (learner);
  if (learner->learning (0)) {
    LOG ("exporting learned empty clause");
    learner->learn (0);
  } else
    LOG ("not exporting learned empty clause");
}

void External::export_learned_unit_clause (Lit ilit) {
  assert (learner);
  if (learner->learning (1)) {
    LOG ("exporting learned unit clause");
    const ELit elit = internal->externalize (ilit);
    assert (elit != INVALID_ELIT);
    learner->learn (elit.signed_representation ());
    learner->learn (0);
  } else
    LOG ("not exporting learned unit clause");
}

void External::export_learned_large_clause (const vector<Lit> &clause) {
  assert (learner);
  size_t size = clause.size ();
  assert (size <= (unsigned) INT_MAX);
  if (learner->learning ((int) size)) {
    LOG ("exporting learned clause of size %zu", size);
    for (auto ilit : clause) {
      const ELit elit = internal->externalize (ilit);
      assert (elit != INVALID_ELIT);
      learner->learn (elit.signed_representation());
    }
    learner->learn (0);
  } else
    LOG ("not exporting learned clause of size %zu", size);
}

signed char &External::external_marked (ELit elit) {
  return ext_flags[elit.var ()];
}

signed char &External::is_extension_var (ELit elit) {
  return ervars[elit.var ()];
}

int64_t &External::external_unit_reason (ELit elit) {
  return ext_units[elit.vlit ()];
}
int64_t External::external_unit_reason (ELit elit) const {
  auto it = ext_units.find (elit.vlit ());
  if (it == ext_units.end ())
    return 0;
  else
    return it->second;
}
} // namespace CaDiCaL
