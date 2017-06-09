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


static const double
one= 1.00000000000000000000e+00,
pS0 = 1.66666666666666657415e-01,
pS1 = -3.25565818622400915405e-01,
pS2 = 2.01212532134862925881e-01,
pS3 = -4.00555345006794114027e-02,
pS4 = 7.91534994289814532176e-04,
pS5 = 3.47933107596021167570e-05,
qS1 = -2.40339491173441421878e+00,
qS2 = 2.02094576023350569471e+00,
qS3 = -6.88283971605453293030e-01,
qS4 = 7.70381505559019352791e-02;

int main()
{
 double z,p,q,r,w,s,c,df,x;
 double one_plus_x;

 //  The following value enforces the division by zero.
 //  x=1.6552276283186724;


     one_plus_x = (one+x);
     z = one_plus_x*0.5;
     p = z*(pS0+z*(pS1+z*(pS2+z*(pS3+z*(pS4+z*pS5)))));
     q = one+z*(qS1+z*(qS2+z*(qS3+z*qS4)));
     if (q == 0)
             printf("Division by 0.\n");
     r = p/q;
     return 0;
}
