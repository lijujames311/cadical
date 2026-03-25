#ifndef _literals_hpp_INCLUDED
#define _literals_hpp_INCLUDED

#include <limits.h>
#include <assert.h>
#include <math.h>

#ifdef LITERAL64
#include <stdint.h>
#endif

#ifdef __cplusplus

#ifdef LITERAL64
#define VAR	 "ld"
#else
#define VAR	 "d"
#endif

//namespace CaDiCaL {
#endif

#ifdef __cplusplus
extern "C" {
#endif
#ifndef LITERAL64
  typedef int ibase_type;
#else
  typedef int64_t ibase_type;
#endif

struct Lit {

#ifdef __cplusplus
  using base_type = ibase_type;
#endif
  ibase_type lit;

  // The parameter must a value encoded as a dimacs literal.
#ifdef __cplusplus
  explicit
  Lit (int v) {
    lit = v;
  };

  // creates an invalid literal
  explicit Lit () : lit (0) {};
  Lit (const Lit&) = default;
  Lit (Lit&&) = default;
  Lit &operator= (const Lit &) = default;
  Lit &operator= (Lit &&) = default;
  ~Lit () = default;
  #define CPPCONST const


  base_type var () const {
    return std::abs (lit);
  }

  Lit operator- () CPPCONST {
    Lit l = *this;
    l.lit = -lit;
    return l;
  }

  bool operator < (const Lit &b) CPPCONST {
    return this->lit < b.lit;
  }
  bool operator <= (const Lit &b) CPPCONST {
    return this->lit <= b.lit;
  }
  bool operator > (const Lit &b) CPPCONST {
    return this->lit > b.lit;
  }
  bool operator >= (const Lit &b) CPPCONST {
    return this->lit >= b.lit;
  }
  bool operator == (const Lit &b) CPPCONST {
    return this->lit == b.lit;
  }
  bool operator != (const Lit &b) CPPCONST {
    return this->lit != b.lit;
  }
  bool valid () CPPCONST {
    return lit && lit != INT_MIN;
  }
  signed char sign () CPPCONST {
    return (lit > 0) - (lit < 0);
  }
  unsigned bign () CPPCONST {
    return 1 + (lit < 0);
  }

  bool is_negated () CPPCONST {
    return lit < 0;
  }
  bool is_positive () CPPCONST {
    return lit > 0;
  }
  Lit operator ^ (const Lit &b) CPPCONST {
    return Lit (lit ^ b.lit);
  }

  // conversion to other representation
  //
  // Conversion to normal dimacs representation
  int signed_representation () CPPCONST {
    return lit;
  }

  // index version for arrays for literals
  size_t operator () () const {
    return lit;
  }

  Lit labs () CPPCONST {
    if (lit < 0)
      return Lit (-lit);
    return Lit (lit);
  }
  unsigned vlit () CPPCONST {
    return (is_negated ()) + 2u * (unsigned) var ();
  }
#endif
};


typedef struct Lit CaDiCaL_Lit;

#ifdef __cplusplus
static const Lit INVALID_LIT = Lit();
static const Lit OTHER_INVALID_LIT = Lit(INT_MIN);
#endif

#ifndef LITERAL64
  typedef int ebase_type;
#else
  typedef int64_t ebase_type;
#endif

struct ELit {
#ifdef __cplusplus
  using base_type = ebase_type;
#endif
  ebase_type lit;

  #ifdef __cplusplus
  // We require the variable to be positive such that we are able to change the
  // representation of literals in this class
  explicit ELit (int v) : lit (v) {
  };

  // creates an invalid literal
  explicit ELit () : lit (0) {};
  ELit (const ELit&) = default;
  ELit (ELit&&) = default;
  ELit &operator= (ELit &&) noexcept = default;
  ELit &operator= (const ELit &) noexcept = default;
  ~ELit () = default;

  ebase_type operator () () {
    return lit;
  }

  ebase_type var () const {
    return std::abs (lit);
  }

  ELit operator- () const {
    ELit l = *this;
    l.lit = -lit;
    return l;
  }

  bool operator < (const ELit &b) const {
    return this->lit < b.lit;
  }
  bool operator <= (const ELit &b) const {
    return this->lit <= b.lit;
  }
  bool operator > (const ELit &b) const {
    return this->lit > b.lit;
  }
  bool operator >= (const ELit &b) const {
    return this->lit >= b.lit;
  }
  bool operator == (const ELit &b) const {
    return this->lit == b.lit;
  }
  bool operator != (const ELit &b) const {
    return this->lit != b.lit;
  }
  bool valid () const {
    return lit && lit != INT_MIN;
  }
  signed char sign () const {
    return (lit > 0) - (lit < 0);
  }
  unsigned bign () const {
    return 1 + (lit < 0);
  }

  bool is_negated () const {
    return lit < 0;
  }
  bool is_positive () const {
    return lit > 0;
  }

  Lit operator ^ (const Lit &b) const {
    return Lit (lit ^ b.lit);
  }


  // conversion to other representation
  //
  // Conversion to normal dimacs representation
  int signed_representation () const {
    return lit;
  }

  ELit labs () const {
    if (lit < 0)
      return ELit (-lit);
    return ELit (lit);
  }
  unsigned vlit () const {
    assert (valid ());
    return (is_negated ()) + 2u * (unsigned) var ();
  }
#endif
};


#ifdef __cplusplus
static const ELit INVALID_ELIT = ELit();
static const ELit OTHER_INVALID_ELIT = ELit(INT_MIN);

}


#endif


#ifdef __cplusplus
//}
#endif



#endif
