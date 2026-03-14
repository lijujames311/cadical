#include "internal.hpp"
#include "literals.hpp"

namespace CaDiCaL {

void External::push_zero_on_extension_stack () {
  extension.push_back (0);
  LOG ("pushing 0 on extension stack");
}

void External::push_id_on_extension_stack (int64_t id) {
  const uint32_t higher_bits = static_cast<int> (id << 32);
  const uint32_t lower_bits = (id & (((int64_t) 1 << 32) - 1));
  extension.push_back (higher_bits);
  extension.push_back (lower_bits);
  LOG ("pushing id %" PRIu64 " = %d + %d", id, higher_bits, lower_bits);
}

void External::push_clause_literal_on_extension_stack (Lit ilit) {
  assert (ilit != INVALID_LIT);
  const ELit elit = internal->externalize (ilit);
  assert (elit != INVALID_ELIT);
  extension.push_back (elit.signed_representation());
  LOG ("pushing clause literal %d on extension stack (internal %d)", elit,
       ilit);
}

void External::push_witness_literal_on_extension_stack (Lit ilit) {
  assert (ilit != INVALID_LIT);
  const ELit elit = internal->externalize (ilit);
  assert (elit != INVALID_ELIT);
  extension.push_back (elit.signed_representation());
  LOG ("pushing witness literal %d on extension stack (internal %d)", elit,
       ilit);
  if (marked (witness, elit))
    return;
  LOG ("marking witness %d", elit);
  mark (witness, elit);
}

// The extension stack allows to reconstruct a satisfying assignment for the
// original formula after removing eliminated clauses.  This was pioneered
// by Niklas Soerensson in MiniSAT and for instance is described in our
// inprocessing paper, published at IJCAR'12.  This first function adds a
// clause to this stack.  First the blocking or eliminated literal is added,
// and then the rest of the clause.

void External::push_clause_on_extension_stack (Clause *c) {
  internal->stats.weakened++;
  internal->stats.weakenedlen += c->size;
  push_zero_on_extension_stack ();
  push_id_on_extension_stack (c->id);
  push_zero_on_extension_stack ();
  for (const auto &lit : *c)
    push_clause_literal_on_extension_stack (lit);
}

void External::push_clause_on_extension_stack (Clause *c, Lit pivot) {
  push_zero_on_extension_stack ();
  push_witness_literal_on_extension_stack (pivot);
  push_clause_on_extension_stack (c);
}

void External::push_binary_clause_on_extension_stack (int64_t id, Lit pivot,
                                                      Lit other) {
  internal->stats.weakened++;
  internal->stats.weakenedlen += 2;
  push_zero_on_extension_stack ();
  push_witness_literal_on_extension_stack (pivot);
  push_zero_on_extension_stack ();
  push_id_on_extension_stack (id);
  push_zero_on_extension_stack ();
  push_clause_literal_on_extension_stack (pivot);
  push_clause_literal_on_extension_stack (other);
}

/*------------------------------------------------------------------------*/

void External::push_external_clause_and_witness_on_extension_stack (
    const vector<int> &c, const vector<int> &w, int64_t id) {
  assert (id);
  extension.push_back (0);
  for (const auto &dimacs_lit : w) {
    ELit elit (dimacs_lit);
    assert (elit != OTHER_INVALID_ELIT);
    init (elit);
    extension.push_back (elit.signed_representation());
    mark (witness, elit);
  }
  extension.push_back (0);
  const uint32_t higher_bits = static_cast<int> (id << 32);
  const uint32_t lower_bits = (id & (((int64_t) 1 << 32) - 1));
  extension.push_back (higher_bits);
  extension.push_back (lower_bits);
  extension.push_back (0);
  for (const auto &dimacs_lit : c) {
    ELit elit (dimacs_lit);
    assert (elit != OTHER_INVALID_ELIT);
    init (elit);
    extension.push_back (elit.signed_representation());
  }
}

/*------------------------------------------------------------------------*/

// This is the actual extension process. It goes backward over the clauses
// on the extension stack and flips the assignment of one of the blocking
// literals in the conditional autarky stored before the clause.  In the
// original algorithm for witness construction for variable elimination and
// blocked clause removal the conditional autarky consists of a single
// literal from the removed clause, while in general the autarky witness can
// contain an arbitrary set of literals.  We are using the more general
// witness reconstruction here which for instance would also work for
// super-blocked or set-blocked clauses.

void External::extend () {

  assert (!extended);
  START (extend);
  internal->stats.extensions++;

  PHASE ("extend", internal->stats.extensions,
         "mapping internal %d assignments to %d assignments",
         internal->max_var, max_var);

#ifndef QUIET
  int64_t updated = 0;
#endif
  for (unsigned i = 1; i <= (unsigned) max_var; i++) {
    const Lit ilit = e2i[ELit (i)];
    if (ilit == INVALID_LIT)
      continue;
    if (i >= vals.size ())
      vals.resize (i + 1, false);
    vals[i] = (internal->val (ilit) > 0);
#ifndef QUIET
    updated++;
#endif
  }
  PHASE ("extend", internal->stats.extensions,
         "updated %" PRId64 " external assignments", updated);
  PHASE ("extend", internal->stats.extensions,
         "extending through extension stack of size %zd",
         extension.size ());
  const auto begin = extension.begin ();
  auto i = extension.end ();
#ifndef QUIET
  int64_t flipped = 0;
#endif
  while (i != begin) {
    bool satisfied = false;
    int p;
    assert (i != begin);
    while ((p = *--i)) {
      if (satisfied)
        continue;
      ELit lit (p);
      if (ival (lit) == lit)
        satisfied = true;
      assert (i != begin);
    }
    assert (i != begin);
    LOG ("id=%" PRId64, ((int64_t) *i << 32) + *(i - 1));
    assert (*i || *(i - 1));
    --i;
    assert (i != begin);
    --i;
    assert (i != begin);
    assert (!*i);
    --i;
    assert (i != begin);
    if (satisfied)
      while (*--i)
        assert (i != begin);
    else {
      while ((p = *--i)) {
        ELit lit (p);
        const ELit tmp = ival (lit); // not 'signed char'!!!
        if (tmp != lit) {
          LOG ("flipping blocking literal %d", lit);
          assert (lit != INVALID_ELIT);
          assert (lit != OTHER_INVALID_ELIT);
          size_t idx = std::abs (p);
          if (idx >= vals.size ())
            vals.resize (idx + 1, false);
          vals[idx] = !vals[idx];
          internal->stats.extended++;
#ifndef QUIET
          flipped++;
#endif
        }
        assert (i != begin);
      }
    }
  }
  PHASE ("extend", internal->stats.extensions,
         "flipped %" PRId64 " literals during extension", flipped);
  extended = true;
  LOG ("extended");
  STOP (extend);
}

/*------------------------------------------------------------------------*/

bool External::traverse_witnesses_backward (WitnessIterator &it) {
  if (internal->unsat)
    return true;
  vector<int> clause, witness;
  const auto begin = extension.begin ();
  auto i = extension.end ();
  while (i != begin) {
    int p;
    while ((p = *--i)) {
      ELit lit (p);
      clause.push_back (lit.signed_representation());
    }
    assert (!p);
    --i;
    const int64_t id =
        ((int64_t) * (i - 1) << 32) + static_cast<int64_t> (*i);
    assert (id);
    i -= 2;
    assert (!*i);
    assert (i != begin);
    while ((p = *--i)){
      ELit lit (p);
      witness.push_back (lit.signed_representation());
    }
    reverse (clause.begin (), clause.end ());
    reverse (witness.begin (), witness.end ());
    LOG (clause, "traversing clause");
    if (!it.witness (clause, witness, id))
      return false;
    clause.clear ();
    witness.clear ();
  }
  return true;
}

bool External::traverse_witnesses_forward (WitnessIterator &it) {
  if (internal->unsat)
    return true;
  vector<int> clause, witness;
  const auto end = extension.end ();
  auto i = extension.begin ();
  if (i != end) {
    ELit lit (*i++);
    do {
      assert (lit != INVALID_ELIT), (void) lit;
      while (lit = ELit (*i), *i++)
        witness.push_back (lit.signed_representation ());
      assert (lit != INVALID_ELIT);
      assert (i != end);
      assert (!*i);
      const int64_t id =
          ((int64_t) *i << 32) + static_cast<int64_t> (*(i + 1));
      assert (id > 0);
      i += 3;
      assert (*i);
      assert (i != end);
      while (i != end && (lit = ELit (*i), *i++))
        clause.push_back (lit.signed_representation());
      if (!it.witness (clause, witness, id))
        return false;
      clause.clear ();
      witness.clear ();
    } while (i != end);
  }
  return true;
}

/*------------------------------------------------------------------------*/

void External::conclude_sat () {
  if (!internal->proof || concluded)
    return;
  concluded = true;
  if (!extended)
    extend ();
  vector<int> model;
  for (int idx = 1; idx <= max_var; idx++) {
    if (ervars[idx])
      continue;
    const ELit lit = ival (ELit (idx));
    model.push_back (lit.signed_representation());
  }
  internal->proof->conclude_sat (model);
}

} // namespace CaDiCaL
