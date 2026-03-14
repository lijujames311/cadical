#include "internal.hpp"
#include "literals.hpp"

namespace CaDiCaL {

void Internal::constrain (Lit lit) {
  if (lit != INVALID_LIT)
    constraint.push_back (lit);
  else {
    if (level)
      backtrack_without_updating_phases ();
    LOG (constraint, "shrinking constraint");
    bool satisfied_constraint = false;
    const vector<Lit>::const_iterator end = constraint.end ();
    vector<Lit>::iterator i = constraint.begin ();
    for (vector<Lit>::const_iterator j = i; j != end; j++) {
      int tmp = marked (*j);
      if (tmp > 0) {
        LOG ("removing duplicated literal %s from constraint", LOGLIT (*j));
      } else if (tmp < 0) {
        LOG ("tautological since both %s and %s occur in constraint", LOGLIT (-*j),
             LOGLIT (*j));
        satisfied_constraint = true;
        break;
      } else {
        tmp = val (*j);
        if (tmp < 0) {
          LOG ("removing falsified literal %s from constraint clause", LOGLIT (*j));
        } else if (tmp > 0) {
          LOG ("satisfied constraint with literal %s", LOGLIT (*j));
          satisfied_constraint = true;
          break;
        } else {
          *i++ = *j;
          mark (*j);
        }
      }
    }
    constraint.resize (i - constraint.begin ());
    for (const auto &lit : constraint)
      unmark (lit);
    if (satisfied_constraint)
      constraint.clear ();
    else if (constraint.empty ()) {
      unsat_constraint = true;
      if (!conflict_id)
        marked_failed = false; // allow to trigger failing ()
    } else
      for (const auto lit : constraint)
        freeze (lit);
  }
}

bool Internal::failed_constraint () { return unsat_constraint; }

void Internal::reset_constraint () {
  for (auto lit : constraint)
    melt (lit);
  LOG ("cleared %zd constraint literals", constraint.size ());
  constraint.clear ();
  unsat_constraint = false;
  marked_failed = true;
}

} // namespace CaDiCaL
