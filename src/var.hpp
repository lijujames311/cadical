#ifndef _var_hpp_INCLUDED
#define _var_hpp_INCLUDED

namespace CaDiCaL {

struct Clause;

#ifdef INTERNALLITERAL64
#define LEVEL	 "ld"
#else
#define LEVEL	 "d"
#endif

// This structure captures data associated with an assigned variable.

struct Var {

  // Note that none of these members is valid unless the variable is
  // assigned.  During unassigning a variable we do not reset it.
#ifndef INTERNALLITERAL64
  using Level = int;
  using Trail_Position = int;
  int level;      // decision level
  int trail;      // trail height at assignment
#else
  using Level = std::size_t;
  using Trail_Position = std::size_t;
  std::size_t level;      // decision level
  std::size_t trail;      // trail height at assignment
#endif
  Clause *reason; // implication graph edge during search
};

} // namespace CaDiCaL

#endif
