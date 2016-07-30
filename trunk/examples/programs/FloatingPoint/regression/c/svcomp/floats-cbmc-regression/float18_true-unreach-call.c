extern void __VERIFIER_error(void);
#define _USE_MATH_DEFINES 
#include <math.h>
#ifndef M_PI
# define M_PI		3.14159265358979323846	/* pi */
#endif

int main()
{
   double  s, f=0.0, fStep=0.1*M_PI;
   int     n=0;

   do
   {
       s = sin(f);
       f += fStep;
       n++;
   }
   while( f < M_PI );

   if(!( n < 11 )) __VERIFIER_error();
}


