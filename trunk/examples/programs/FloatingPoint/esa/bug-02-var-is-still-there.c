//#Safe 
/**
 * 2017-10-10 Dietsch: Example for AssertionError: var is still there 
 *  
 * Run with 
 * AutomizerC.xml
 * svcomp-Reach-64bit-Automizer_Bitvector.epf
 * HoenickeLindenmann_1ByteResolution
 * 
 */

typedef union
{
  float value;
  int word;
} ieee_float_shape_type;

int isnan_float(float x) {

   int ix;
   do {
		ieee_float_shape_type gf_u; 
		gf_u.value = x;  
		ix  = gf_u.word; 
	} while (0);
    
   return ix;
}

void main()
{
	int y;
	!isnan_float(y) || isnan_float(0);  

    int res = y;

    if (!isnan_float(y) && res) {
      __VERIFIER_error();
    }
}
