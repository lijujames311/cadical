#include "internal.hpp"

namespace CaDiCaL {

// Sam Buss suggested to debug the case where a solver incorrectly claims
// the formula to be unsatisfiable by checking every learned clause to be
// satisfied by a satisfying assignment.  Thus the first inconsistent
// learned clause will be immediately flagged without the need to generate
// proof traces and perform forward proof checking.  The incorrectly derived
// clause will raise an abort signal and thus allows to debug the issue with
// a symbolic debugger immediately.

void External::check_solution_on_learned_clause () {
  assert (solution);
  for (const auto &lit : internal->clause) {
    auto elit = internal->externalize (lit);
    if (sol (elit) == elit)
      return;
  }
  fatal_message_start ();
  fputs ("learned clause unsatisfied by solution:\n", stderr);
  for (const auto &lit : internal->clause) {
    auto elit = internal->externalize (lit);
    fprintf (stderr, "%" EVAR " ", elit.signed_representation());
  }
  fputc ('0', stderr);
  fatal_message_end ();
}

void External::check_solution_on_shrunken_clause (Clause *c) {
  assert (solution);
  for (const auto &lit : *c) {
    auto elit = internal->externalize (lit);
    if (sol (elit) == elit)
      return;
  }
  fatal_message_start ();
  for (const auto &lit : *c) {
    auto elit = internal->externalize (lit);
    fprintf (stderr, "%" EVAR " ", elit.signed_representation());
  }
  fputc ('0', stderr);
  fatal_message_end ();
}

void External::check_no_solution_after_learning_empty_clause () {
  assert (solution);
  FATAL ("learned empty clause but got solution");
}

void External::check_solution_on_learned_unit_clause (Lit unit) {
  assert (solution);
  auto eunit = internal->externalize (unit);
  if (sol (eunit) == eunit)
    return;
  FATAL ("learned unit %" EVAR " contradicts solution", (eunit).signed_representation());
}

} // namespace CaDiCaL
