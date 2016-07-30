extern void __VERIFIER_error(void);

int main(void)
{
  float f   = -0x1.0p-127f;
  double d  = -0x1.0p-127;
  double fp = (double)f;

  if(!(d == fp)) __VERIFIER_error();

  return 0;
}
