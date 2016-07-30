extern void __VERIFIER_assume(int);
extern void __VERIFIER_error(void);
int main()
{
  // constants
  if(!(1.0!=2.0)) __VERIFIER_error();
  if(!(1.0==1.0)) __VERIFIER_error();
  if(!(1.0<2.0)) __VERIFIER_error();
  if(!(!(-1.0<-2.0))) __VERIFIER_error();
  if(!(2.0>1.0)) __VERIFIER_error();
  if(!(!(-2.0>-1.0))) __VERIFIER_error();
  if(!(!(2.0<2.0))) __VERIFIER_error();
  if(!(!(-2.0<-2.0))) __VERIFIER_error();
  if(!(!(2.0>2.0))) __VERIFIER_error();
  if(!(!(-2.0>-2.0))) __VERIFIER_error();
  if(!(2.0<=2.0)) __VERIFIER_error();
  if(!(-2.0<=-2.0)) __VERIFIER_error();
  if(!(2.0>=2.0)) __VERIFIER_error();
  if(!(-2.0>=-2.0)) __VERIFIER_error();
  if(!(1.0<=2.0)) __VERIFIER_error();
  if(!(!(-1.0<=-2.0))) __VERIFIER_error();
  if(!(2.0>=1.0)) __VERIFIER_error();
  if(!(!(-2.0>=-1.0))) __VERIFIER_error();  
  
  // variables
  float a, b, _a=a, _b=b;
  __VERIFIER_assume(a==1 && b==2);

  if(!(a!=b)) __VERIFIER_error();
  if(!(a==a)) __VERIFIER_error();
  if(!(a<b)) __VERIFIER_error();
  if(!(!(-a<-b))) __VERIFIER_error();
  if(!(b>a)) __VERIFIER_error();
  if(!(!(-b>-a))) __VERIFIER_error();
  if(!(!(b<b))) __VERIFIER_error();
  if(!(!(-b<-b))) __VERIFIER_error();
  if(!(!(b>b))) __VERIFIER_error();
  if(!(!(-b>-b))) __VERIFIER_error();
  if(!(b<=b)) __VERIFIER_error();
  if(!(-b<=-b)) __VERIFIER_error();
  if(!(b>=b)) __VERIFIER_error();
  if(!(-b>=-b)) __VERIFIER_error();
  if(!(a<=b)) __VERIFIER_error();
  if(!(!(-a<=-b))) __VERIFIER_error();
  if(!(b>=a)) __VERIFIER_error();
  if(!(!(-b>=-a))) __VERIFIER_error();  
}
