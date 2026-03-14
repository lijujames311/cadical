#ifndef _sweep_hpp_INCLUDED
#define _sweep_hpp_INCLUDED

#include "literals.hpp"
#include "random.hpp"
#include <cstdint>
#include <vector>

namespace CaDiCaL {

struct Internal;

struct sweep_proof_clause {
  unsigned sweep_id; // index for sweeper.clauses
  int64_t cad_id;    // cadical id
  unsigned kit_id;   // kitten id
  bool learned;
  std::vector<Lit> literals;
  std::vector<unsigned> chain; // lrat
};

struct sweep_blocked_clause {
  int64_t id;
  std::vector<int> literals;
};

struct sweep_binary {
  Lit lit;
  Lit other;
  int64_t id;
};

struct Clause;

struct Sweeper {
  Sweeper (Internal *internal);
  ~Sweeper ();
  Internal *internal;
  Random random;
  std::vector<unsigned> depths;
  Lit *reprs;
  std::vector<Lit> next, prev;
  Lit first, last;
  unsigned encoded;
  unsigned save;
  std::vector<Lit> vars;
  std::vector<Clause *> clauses;
  std::vector<sweep_blocked_clause> blocked_clauses;
  std::vector<Lit> blockable;
  std::vector<Lit> clause;
  std::vector<Lit> propagate;
  std::vector<Lit> backbone;
  std::vector<Lit> partition;
  std::vector<bool> prev_units;
  std::vector<sweep_binary> binaries;
  std::vector<sweep_proof_clause> core[2];
  uint64_t current_ticks;
  struct {
    uint64_t ticks;
    unsigned clauses, depth, vars;
  } limit;
};

} // namespace CaDiCaL

#endif
