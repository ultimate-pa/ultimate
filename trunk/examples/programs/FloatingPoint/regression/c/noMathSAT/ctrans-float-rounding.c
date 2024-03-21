//#Safe
/*  
   Extract from floats-cbmc-regression/float-rounding-1.i 
   
   We found a FailurePath: 
   [L43]              float f1 = 0x1.0p+0;
   [L44]              float f2 = 0x1.8p-24;
          VAL         [f1=1.0, f2=0.00000008940696716308594]
   [L46]  CALL        roundingTest(f1,f2)
          VAL         [\old(f1)=1.0, \old(f2)=0.00000008940696716308594]
   [L29]              float roundToNearestSum = f1 + f2;
          VAL         [\old(f1)=1.0, \old(f2)=0.00000008940696716308594, f1=1.0, f2=0.00000008940696716308594, roundToNearestSum=1.0000001192092896]
   [L30]  COND FALSE  !(!(roundToNearestSum == 0x1.000002p+0f))
          VAL         [\old(f1)=1.0, \old(f2)=0.00000008940696716308594, f1=1.0, f2=0.00000008940696716308594, roundToNearestSum=1.0000001192092896]
   [L34]              float roundDownSum = f1 + f2;
          VAL         [\old(f1)=1.0, \old(f2)=0.00000008940696716308594, f1=1.0, f2=0.00000008940696716308594, roundDownSum=1.0000001192092896, roundToNearestSum=1.0000001192092896]
   [L35]  COND TRUE   !(roundDownSum == 0x1.0p+0f)
          VAL         [\old(f1)=1.0, \old(f2)=0.00000008940696716308594, f1=1.0, f2=0.00000008940696716308594, roundDownSum=1.0000001192092896, roundToNearestSum=1.0000001192092896]
   [L35]              __VERIFIER_error()
          VAL         [\old(f1)=1.0, \old(f2)=0.00000008940696716308594, f1=1.0, f2=0.00000008940696716308594, roundDownSum=1.0000001192092896, roundToNearestSum=1.0000001192092896]
   
   
   
   0x1.0p+0 is a hexadecimal floating point literal introduced in C99. 
   
   --
   Section 6.4.4.2 of C99:

   A floating constant has a significand part that may be followed by an exponent part and a suffix that specifies its type. The components of the significand part may include a digit sequence representing the whole-number part, followed by a period (.), followed by a digit sequence representing the fraction part.
   
   The components of the exponent part are an e, E, p, or P followed by an exponent consisting of an optionally signed digit sequence. Either the whole-number part or the fraction part has to be present; for decimal floating constants, either the period or the exponent part has to be present.
   
   The significand part is interpreted as a (decimal or hexadecimal) rational number; the digit sequence in the exponent part is interpreted as a decimal integer. For decimal floating constants, the exponent indicates the power of 10 by which the significand part is to be scaled. For hexadecimal floating constants, the exponent indicates the power of 2 by which the significand part is to be scaled.
   
   For decimal floating constants, and also for hexadecimal floating constants when FLT_RADIX is not a power of 2, the result is either the nearest representable value, or the larger or smaller representable value immediately adjacent to the nearest representable value, chosen in an implementation-defined manner. For hexadecimal floating constants when FLT_RADIX is a power of 2, the result is correctly rounded.
   
   The p separates the base number from the exponent. 
   0x1.0 is the significand with optional fraction
   the exponent is the power of 2 by which it is scaled 
   --
   
   This means that 
   0x1.0p+0         == 1.000000000000000000000000000000
   0x1.8p-24        == 0.000000089406967163085937500000
     OUR VALUE:     f2=0.00000008940696716308594
   0x1.000002p+0f   == 1.000000119209289550781250000000
   
*/
#include <math.h>
#include <fenv.h>

extern void __VERIFIER_error(void);

void roundingTest (float f1, float f2) {
  fesetround(0);

  float roundToNearestSum = f1 + f2;
  if(!(roundToNearestSum == 0x1.000002p+0f)) __VERIFIER_error();

  fesetround(0x400);

  float roundDownSum = f1 + f2;
  if(!(roundDownSum == 0x1.0p+0f)) __VERIFIER_error();

  return;
}

int main (void)
{

  float f1 = 0x1.0p+0;
  float f2 = 0x1.8p-24;

  roundingTest(f1,f2);
  return 0;
}
