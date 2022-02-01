//#Safe
/*
 * Casts for IEEE 754 flots that are also correct for reals.
 * 
 * Date: 2017-05-30
 * Author: Matthias Heizmann
 */
int main()
{
  double twoF = 2.0;
  int twoI = 2;
  
  double flowtFromInt = (double) twoI;
  if (flowtFromInt != twoI) {
	  //@assert \false;
  }
  
  int intFromFloat = (int) twoF;
  if (intFromFloat != twoI) {
	  //@assert \false;
  }
  
  double floatFromFloat = (float) twoF;
  if (floatFromFloat != 2.0f) {
	  //@assert \false;
  }

  return 0;
}
