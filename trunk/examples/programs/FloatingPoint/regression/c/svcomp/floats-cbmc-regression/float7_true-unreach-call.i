extern void __VERIFIER_error(void);
int main()
{
  unsigned int i;
  i=0;

  float *p;
  p=(float *)&i;

  float f=*p;

  if(!(f==0.0)) __VERIFIER_error();
}
