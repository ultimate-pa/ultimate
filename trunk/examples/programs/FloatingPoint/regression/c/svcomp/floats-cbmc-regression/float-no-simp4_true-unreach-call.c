extern void __VERIFIER_assume(int);
#include <math.h>
extern void __VERIFIER_error(void);
extern double __VERIFIER_nondet_double();
// all classification

int main()
{
  double d1 = __VERIFIER_nondet_double();
  double _d1 = __VERIFIER_nondet_double();
  d1=_d1;
  __VERIFIER_assume(isnormal(d1));
  if(!(!isnan(d1))) __VERIFIER_error();
  if(!(!isinf(d1))) __VERIFIER_error();
  if(!(isfinite(d1))) __VERIFIER_error();

  double d2 = __VERIFIER_nondet_double();
  double _d2 = __VERIFIER_nondet_double();
  d2=_d2;
  __VERIFIER_assume(isinf(d2));
  if(!(!isnormal(d2))) __VERIFIER_error();
  if(!(!isnan(d2))) __VERIFIER_error();


  double d3 = __VERIFIER_nondet_double();
  double _d3 = __VERIFIER_nondet_double();
  d3=_d3;
  __VERIFIER_assume(isnan(d3));
  if(!(!isnormal(d3))) __VERIFIER_error();
  if(!(!isinf(d3))) __VERIFIER_error();
  if(!(d3!=d3)) __VERIFIER_error();


  double d4 = __VERIFIER_nondet_double();
  double _d4 = __VERIFIER_nondet_double();
  d4=_d4;
  __VERIFIER_assume(isfinite(d4));
  if(!(!isnan(d4))) __VERIFIER_error();
  if(!(!isinf(d4))) __VERIFIER_error();


  double d5 = __VERIFIER_nondet_double();
  double _d5 = __VERIFIER_nondet_double();
  d5=_d5;
  __VERIFIER_assume(!isnan(d5) && !isinf(d5));
  if(!(isfinite(d5))) __VERIFIER_error();
}
