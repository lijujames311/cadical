#ifndef _proof_h_INCLUDED
#define _proof_h_INCLUDED

#include "literals.hpp"
#include "tracer.hpp"
#include <stdint.h>

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

class File;
struct Clause;
struct Internal;
class Tracer;
class FileTracer;

/*------------------------------------------------------------------------*/

// Provides proof checking and writing.

class Proof {

  Internal *internal;

  std::vector<int> clause;          // of external literals
  std::vector<int64_t> proof_chain; // LRAT style proof chain of clause
  int64_t clause_id;                // id of added clause
  bool redundant;
  int witness;

  // the 'tracers'
  std::vector<Tracer *> tracers;          // tracers (ie checker)
  std::vector<FileTracer *> file_tracers; // file tracers (ie LRAT tracer)

  void add_literal (Lit internal_lit); // add to 'clause'
  void add_literals (Clause *);        // add to 'clause'

  void add_literals (const std::vector<Lit> &); // ditto

  void add_original_clause (
      bool restore = false); // notify observers of original clauses
  void add_derived_clause ();
  void add_assumption_clause ();
  void delete_clause ();
  void demote_clause ();
  void weaken_minus ();
  void strengthen ();
  void finalize_clause ();
  void add_assumption ();
  void add_constraint ();

public:
  Proof (Internal *);
  ~Proof ();

  void connect (Tracer *t) { tracers.push_back (t); }
  void disconnect (Tracer *t);
  // Add original clauses to the proof (for online proof checking).
  //
  void add_original_clause (int64_t, bool, const std::vector<Lit> &);

  void add_assumption_clause (int64_t, const std::vector<ELit> &,
                              const std::vector<int64_t> &);
  void add_assumption_clause (int64_t, ELit, const std::vector<int64_t> &);
  void add_assumption (ELit);
  void add_constraint (const std::vector<ELit> &);
  void reset_assumptions ();

  // Add/delete original clauses to/from the proof using their original
  //  external literals (from external->eclause)
  //
  void add_external_original_clause (int64_t, bool,
                                     const std::vector<ELit> &,
                                     bool restore = false);
  void delete_external_original_clause (int64_t, bool,
                                        const std::vector<ELit> &);

  // Add derived (such as learned) clauses to the proof.
  //
  void add_derived_empty_clause (int64_t, const std::vector<int64_t> &);
  void add_derived_unit_clause (int64_t, Lit unit,
                                const std::vector<int64_t> &);
  void add_derived_clause (Clause *c, const std::vector<int64_t> &);
  void add_derived_clause (int64_t, bool, const std::vector<Lit> &,
                           const std::vector<int64_t> &);
  void add_derived_rat_clause (int64_t, bool, ELit, const std::vector<Lit> &,
                               const std::vector<int64_t> &);
  void add_derived_rat_clause (Clause *c, ELit w,
                               const std::vector<int64_t> &);

  // deletion of clauses. It comes in several variants, depending if the
  // clause should be restored or not
  void delete_clause (int64_t, bool, const std::vector<Lit> &);
  void weaken_minus (int64_t, const std::vector<Lit> &);
  void weaken_plus (int64_t, const std::vector<Lit> &);
  void delete_unit_clause (int64_t id, const Lit lit);
  void delete_clause (Clause *);
  void weaken_minus (Clause *);
  void weaken_plus (Clause *);
  void strengthen (int64_t);

  void finalize_unit (int64_t, Lit);
  void finalize_external_unit (int64_t, ELit);
  void finalize_clause (int64_t, const std::vector<Lit> &c);
  void finalize_clause (Clause *);

  void report_status (int, int64_t);
  void begin_proof (int64_t);
  void conclude_unsat (ConclusionType, const std::vector<int64_t> &);
  void conclude_sat (const std::vector<int> &model);
  void conclude_unknown (const std::vector<int> &trace);
  void solve_query ();
  // These two actually pretend to add and remove a clause.
  //
  void flush_clause (Clause *); // remove falsified literals
  void strengthen_clause (Clause *, Lit, const std::vector<int64_t> &);
  void otfs_strengthen_clause (Clause *, const std::vector<Lit> &,
                               const std::vector<int64_t> &);

  void flush ();
};

} // namespace CaDiCaL

#endif
