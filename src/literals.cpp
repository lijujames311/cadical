#include "literals.hpp"

#include <cmath>

#ifdef __cplusplus

namespace CaDiCaL {
Lit::base_type abs (Lit a) {
  return a.var ();
}

Lit operator*(int sign, Lit lit) {
    assert (sign == -1 || sign == 1);
    return Lit (lit.lit * sign);
}

ELit operator*(int sign, ELit lit) {
    assert (sign == -1 || sign == 1);
    return ELit (lit.lit * sign);
}

Lit::base_type abs (Lit::base_type lit) {
#ifdef LITERAL64
  return lit < 0 ? -lit : lit;
#else
  return std::abs (lit);
#endif
}
}
#endif
