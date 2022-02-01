extern void __VERIFIER_error(void);

void multiply(void)
{
  float f1=0x1.000000p-1f;
  float f2=0x1.fffffep-126f;

  float res = f1 * f2;

  if(!(res == 0x1.0p-126f)) __VERIFIER_error();
}

void divide(void)
{
  float f1=0x1.000000p+1f;
  float f2=0x1.fffffep-126f;

  float res = f2 / f1;

  if(!(res == 0x1.0p-126f)) __VERIFIER_error();
}

void cast(void)
{
  double d = 0x1.fffffep-127;

  float f = (float)d;

  if(!(f == 0x1.0p-126f)) __VERIFIER_error();
}

int main()
{
  multiply();
  divide();
  cast();
}
