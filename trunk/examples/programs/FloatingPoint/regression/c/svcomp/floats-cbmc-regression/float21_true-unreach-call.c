extern void __VERIFIER_assume(int);
extern void __VERIFIER_error(void);
/*
** subnormal-boundary.c
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 25/07/12
**
** Regression tests for casting and classification around the subnormal boundary.
**
*/

#include <math.h>

float __VERIFIER_nondet_float(void);

int main (void)
{
  #ifdef __GNUC__

  float smallestNormalFloat = 0x1.0p-126f;
  float largestSubnormalFloat = 0x1.fffffcp-127f;
  
  double v = 0x1.FFFFFFp-127;

  float f;


  // Check the encodings are correct
  if(!(fpclassify(largestSubnormalFloat) == FP_SUBNORMAL)) __VERIFIER_error();

  f = __VERIFIER_nondet_float();
  __VERIFIER_assume(fpclassify(f) == FP_SUBNORMAL);
  if(!(f <= largestSubnormalFloat)) __VERIFIER_error();


  if(!(fpclassify(smallestNormalFloat) == FP_NORMAL)) __VERIFIER_error();

  f = __VERIFIER_nondet_float();
  __VERIFIER_assume(fpclassify(f) == FP_NORMAL);
  if(!(smallestNormalFloat <= fabs(f))) __VERIFIER_error();

  if(!(largestSubnormalFloat < smallestNormalFloat)) __VERIFIER_error();


  // Check the ordering as doubles
  if(!(((double)largestSubnormalFloat) < ((double)smallestNormalFloat))) __VERIFIER_error();
  if(!(((double)largestSubnormalFloat) < v)) __VERIFIER_error();
  if(!(v < ((double)smallestNormalFloat))) __VERIFIER_error();


  // Check coercion to float
  if(!((float)((double)largestSubnormalFloat) == largestSubnormalFloat)) __VERIFIER_error();
  if(!((float)((double)smallestNormalFloat) == smallestNormalFloat)) __VERIFIER_error();

  if(!(((double)smallestNormalFloat) - v <= v - ((double)largestSubnormalFloat))) __VERIFIER_error();
  if(!(((float)v) == smallestNormalFloat)) __VERIFIER_error();

  f = __VERIFIER_nondet_float();
  __VERIFIER_assume(fpclassify(f) == FP_SUBNORMAL);
  if(!( ((float)((double)f)) == f )) __VERIFIER_error();
  
  #endif

  return 0;
}
