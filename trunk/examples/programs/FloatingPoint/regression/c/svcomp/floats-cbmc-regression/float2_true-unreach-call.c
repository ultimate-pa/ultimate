extern void __VERIFIER_error(void);

int main()
{
  float a;
  double b;

  // various forms of floating-point literals
  a=1.25L;
  if(!(a==1.25)) __VERIFIER_error();

  b=1.250;
  if(!(b==1.25)) __VERIFIER_error();
  
  // with exponent
  a=0.5e2;
  if(!(a==50)) __VERIFIER_error();

  // hex
  a=0x1.4p+4;
  if(!(a==20)) __VERIFIER_error();
}
