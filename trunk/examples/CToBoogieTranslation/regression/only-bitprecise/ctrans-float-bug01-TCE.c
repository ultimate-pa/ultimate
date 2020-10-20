/**
 * Memory access to union of double and int leads to conversion error between SMT float and bv 
 *
 */

typedef union {
  double value;
  struct {

    int msw;
  } parts;
} ieee_double_shape_type;

void isfinite_double( ) {
  int hx;
  ieee_double_shape_type gh_u;
  hx  = gh_u.parts.msw;

}