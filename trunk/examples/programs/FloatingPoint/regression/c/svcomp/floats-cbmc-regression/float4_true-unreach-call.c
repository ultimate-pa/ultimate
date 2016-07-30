extern void __VERIFIER_assume(int);
#include <math.h>
extern void __VERIFIER_error(void);
int main()
{
  double f, f2;
  // the following rely on f not being a NaN or Infinity
  __VERIFIER_assume(!isnan(f2));
  __VERIFIER_assume(!isinf(f2));
  f=f2;
  
  // addition
  if(!(100.0+10==110)) __VERIFIER_error();
  if(!(0+f==f)) __VERIFIER_error();
  if(!(f+0==f)) __VERIFIER_error();
  if(!(100+0.5==100.5)) __VERIFIER_error();
  if(!(0.0+0.0+f==f)) __VERIFIER_error();
  
  // subtraction
  if(!(100.0-10==90)) __VERIFIER_error();
  if(!(0-f==-f)) __VERIFIER_error();
  if(!(f-0==f)) __VERIFIER_error();
  if(!(100-0.5==99.5)) __VERIFIER_error();
  if(!(0.0-0.0-f==-f)) __VERIFIER_error();

  // unary minus
  if(!(-(-100.0)==100)) __VERIFIER_error();
  if(!(-(1-2.0)==1)) __VERIFIER_error();
  if(!(-(-f)==f)) __VERIFIER_error();

  // multiplication
  if(!(100.0*10==1000)) __VERIFIER_error();
  if(!(0*f==0)) __VERIFIER_error();
  if(!(f*0==0)) __VERIFIER_error();
  if(!(100*0.5==50)) __VERIFIER_error();
  if(!(f*1==f)) __VERIFIER_error();
  if(!(1*f==f)) __VERIFIER_error();
  if(!(1.0*1.0*f==f)) __VERIFIER_error();

  // division
  if(!(100.0/1.0==100)) __VERIFIER_error();
  if(!(100.1/1.0==100.1)) __VERIFIER_error();
  if(!(100.0/2.0==50)) __VERIFIER_error();
  if(!(100.0/0.5==200)) __VERIFIER_error();
  if(!(0/1.0==0)) __VERIFIER_error();
  if(!(f/1.0==f)) __VERIFIER_error();
  
  // conversion
  if(!(((double)(float)100)==100.0)) __VERIFIER_error();
  if(!(((unsigned int)100.0)==100.0)) __VERIFIER_error();
  if(!(100.0)) __VERIFIER_error();
  if(!(!0.0)) __VERIFIER_error();
  if(!((int)0.5==0)) __VERIFIER_error();
  if(!((int)0.49==0)) __VERIFIER_error();
  if(!((int)-1.5==-1)) __VERIFIER_error();
  if(!((int)-10.49==-10)) __VERIFIER_error();
  
  // relations
  if(!(1.0<2.5)) __VERIFIER_error();
  if(!(1.0<=2.5)) __VERIFIER_error();
  if(!(1.01<=1.01)) __VERIFIER_error();
  if(!(2.5>1.0)) __VERIFIER_error();
  if(!(2.5>=1.0)) __VERIFIER_error();
  if(!(1.01>=1.01)) __VERIFIER_error();
  if(!(!(1.0>=2.5))) __VERIFIER_error();
  if(!(!(1.0>2.5))) __VERIFIER_error();
  if(!(1.0!=2.5)) __VERIFIER_error();
}
