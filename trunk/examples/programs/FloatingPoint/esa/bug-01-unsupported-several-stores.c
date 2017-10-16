//#Safe
/*
 * 2017-10-10 Dietsch: Example for "UnsupportedOperationException: unsupported: several stores"
 * Run with 
 * AutomizerC.xml
 * svcomp-Reach-64bit-Automizer_Bitvector.epf
 * HoenickeLindenmann_1ByteResolution
 * 
 */

#include <math.h>

typedef union
{
   float value;
   unsigned int word;
} float_type;

int isinf_float(float x) {
  int ix;
  do { 
	float_type gf_u; 
	gf_u.value = (x); 
	(ix) = gf_u.word; 
  } while (0);
  ix &= 0x7fffffff;
  return ((ix)==0x7f800000L);
}

int main() {
   float x = INFINITY;

   if (!isinf_float(x)) {
    __VERIFIER_error();
   }

  return 0;
}