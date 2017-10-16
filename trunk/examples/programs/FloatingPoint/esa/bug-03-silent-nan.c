//#Safe
/**
 * 2017-10-10 Dietsch: Example for NaN issue. Should be safe but we say unsafe, probably because we do not distinguish between silent and signalling NaN. 
 * 
 * Run with 
 * AutomizerC.xml
 * svcomp-Reach-64bit-Automizer_Bitvector.epf
 * HoenickeLindenmann_1ByteResolution
 * 
 * From http://smtlib.cs.uiowa.edu/theories-FloatingPoint.shtml
 * -- 
 * "All function symbols with declaration of the form
 * 
 *   ((_ NaN eb sb) (_ FloatingPoint eb sb))
 * 
 *  where eb and sb are numerals greater than 1."
 *  
 * "For each eb and sb, there is exactly one NaN in the set denoted by 
 *  (_ FloatingPoint eb sb), in agreeement with Level 2 of IEEE 754-2008
 *  (floating-point data). There is no distinction in this theory between 
 *  a ``quiet'' and a ``signaling'' NaN.
 *  NaN has several representations, e.g.,(_ NaN eb sb) and any term of 
 *  the form (fp t #b1..1 s) where s is a binary containing at least a 1
 *  and t is either #b0 or #b1."
 * --  
 * 
 */
#include <math.h>

typedef union
{
  float value;
  unsigned int word;
} float_type;

int isnann(float x)
{
	int ix;
	do { 
		float_type gf_u; 
		gf_u.value = (x); 
		(ix) = gf_u.word; 
	} while (0);
	ix &= 0x7fffffff;
	return ((ix)>0x7f800000L);
}

int main()
{
	float x = NAN;

	if (!isnann(x))
	{
		__VERIFIER_error();
	}
}