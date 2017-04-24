extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
int main()
{
  float IN;
  __VERIFIER_assume(IN >= 0.0f && IN < 1.0f);

  float x = IN;

  int i = 0;
  int a = 1;
  int b = 42;

  float result = 1.0f + 0.5f*x - 0.125f*x*x + 0.0625f*x*x*x - 0.0390625f*x*x*x*x;


  while (i < 10000)
  {
        i=a;
        a++;
        while (b < 0)
        {
           b = 42;
        }
  }

  if(!(result >= 0.0f && result < 1.0f && b == 42 && i == 10000))
    __VERIFIER_error();

  return 0;
}
