extern void __VERIFIER_error(void);
extern double __VERIFIER_nondet_double();

#include <math.h>
#include <float.h>

int main()
{
  double d = __VERIFIER_nondet_double();

  #ifndef _MSC_VER

  // first check constants
  
  if(!(isnormal(FLT_MAX))) __VERIFIER_error();
  if(!(isinf(HUGE_VAL))) __VERIFIER_error();
  if(!(isinf(HUGE_VALF))) __VERIFIER_error();
//  if(!(isinf(HUGE_VALL))) __VERIFIER_error();
  if(!(isinf(INFINITY))) __VERIFIER_error();
  if(!(isnan(NAN))) __VERIFIER_error();

  // check +
  if(!(isinf(INFINITY+INFINITY))) __VERIFIER_error();
  if(!(isnan(-INFINITY+INFINITY))) __VERIFIER_error();
  if(!(INFINITY+INFINITY>0)) __VERIFIER_error();
  if(!(isnan(NAN+d))) __VERIFIER_error();
  if(!(isnan(NAN+INFINITY))) __VERIFIER_error();

  // check -
  if(!(isnan(INFINITY-INFINITY))) __VERIFIER_error();
  if(!(isinf(-INFINITY-INFINITY))) __VERIFIER_error();
  if(!(-INFINITY-INFINITY<0)) __VERIFIER_error();
  if(!(isnan(NAN-d))) __VERIFIER_error();
  if(!(isnan(NAN-INFINITY))) __VERIFIER_error();

  // check *
  if(!(isinf(INFINITY*INFINITY))) __VERIFIER_error();
  if(!(isinf(-INFINITY*INFINITY))) __VERIFIER_error();
  if(!(INFINITY*INFINITY>0)) __VERIFIER_error();
  if(!(-INFINITY*INFINITY<0)) __VERIFIER_error();
  if(!(isnan(NAN*d))) __VERIFIER_error();
  if(!(isnan(NAN*INFINITY))) __VERIFIER_error();
  if(!(isnan(INFINITY*0))) __VERIFIER_error();
  if(!(signbit(1.0*-0.0))) __VERIFIER_error();
  if(!(!signbit(1.0*0.0))) __VERIFIER_error();

  // check /
  if(!(isnan(INFINITY/INFINITY))) __VERIFIER_error();
  if(!(isnan(-INFINITY/INFINITY))) __VERIFIER_error();
  // work around compiler warning
  int zero=0;
  if(!(isinf(INFINITY/zero))) __VERIFIER_error();
  if(!(0.0/INFINITY==0)) __VERIFIER_error();
  if(!(1.0/INFINITY==0)) __VERIFIER_error();
  if(!(signbit(-1.0/INFINITY))) __VERIFIER_error();
  if(!(signbit(1.0/-INFINITY))) __VERIFIER_error();
  if(!(INFINITY/-2<0)) __VERIFIER_error();
  if(!(isinf(1.0/0.0))) __VERIFIER_error();
  if(!(isinf(INFINITY/2))) __VERIFIER_error();
  if(!(isnan(0.0/0.0))) __VERIFIER_error();
  if(!(isnan(NAN/d))) __VERIFIER_error();
  if(!(isnan(NAN/INFINITY))) __VERIFIER_error();
  if(!(signbit(-0.0/1))) __VERIFIER_error();

  #endif
}
