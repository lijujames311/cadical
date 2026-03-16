#ifndef _hash_literals_hpp_INCLUDED
#define _hash_literals_hpp_INCLUDED

/*------------------------------------------------------------------------*/
#include "literals.hpp"
#include <functional>

namespace std {
template <>
struct hash<Lit>
{
  std::size_t operator()(const Lit& s) const noexcept
  {
    return std::hash<Lit::base_type>{}(s.lit);
  }
};

template <>
struct hash<ELit>
{
  std::size_t operator()(const ELit& s) const noexcept
  {
    return std::hash<ELit::base_type>{}(s.lit);
  }
};

}

namespace CaDiCaL {

  Lit::base_type abs (Lit a);
  Lit operator*(int sign, Lit lit);
  ELit::base_type abs (ELit a);
  ELit operator*(int sign, ELit lit);
  Lit::base_type abs (Lit::base_type a);

}
#endif
