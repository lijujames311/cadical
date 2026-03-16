#include "literals.hpp"

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

}
#endif
