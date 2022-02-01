//#Unsafe
/*
 * Date: 2017-06-09
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Part of esa_01_newlib.c extracted by Marius to show
 * there can be some division by zero.
 *
 */


#include <stdio.h>

int main()
{
 double z,p,q,r,w,s,c,df,x;
 double one_plus_x;

 //  The following value enforces the division by zero.
 //  x=1.6552276283186724;


     one_plus_x = (1.00000000000000000000e+00+x);
     z = one_plus_x*0.5;
     q = 1.00000000000000000000e+00+z*(-2.40339491173441421878e+00+z*(2.02094576023350569471e+00+z*(-6.88283971605453293030e-01+z*7.70381505559019352791e-02)));
     if (q == 0) {
         printf("Division by 0.\n");
         //@ assert \false;
     }
     return 0;
}
