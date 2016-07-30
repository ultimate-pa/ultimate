extern void __VERIFIER_assume(int);
extern void __VERIFIER_error(void);
int main()
{
  float a, b;
  
  __VERIFIER_assume(a==1 || a==0.5 || a==2 || a==3 || a==0.1);
  b=a;
  a/=2;
  a*=2;
  if(!(a==b)) __VERIFIER_error();
}
