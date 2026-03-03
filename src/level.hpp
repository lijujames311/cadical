#ifndef _level_hpp_INCLUDED
#define _level_hpp_INCLUDED

#include <climits>

namespace CaDiCaL {

// For each new decision we increase the decision level and push a 'Level'
// on the 'control' stack.  The information gathered here is used in
// 'reuse_trail' and for early aborts in clause minimization.

struct Level {

  int decision; // decision literal of this level
  int trail;    // trail start of this level

  struct {
    int count; // how many variables seen during 'analyze'
    int trail; // smallest trail position seen on this level
  } seen;

  void reset () {
    seen.count = 0;
    seen.trail = INT_MAX;
  }

  Level (int d, int t) : decision (d), trail (t) { reset (); }
  Level () {}
};

struct CtxLevel {
  int act_elit = 0; // external activator variable
  int activator = 0; // Activating assumption literal of that level (ilit!)
  
  Clause *reason = 0; // The clause that propagates the activator literal

  size_t stack_size = 0;
  
  CtxLevel (int elit) : act_elit(elit) {};
  CtxLevel () {};

  bool is_empty_level () const {
    return act_elit == 0;
  }
};

} // namespace CaDiCaL

#endif
