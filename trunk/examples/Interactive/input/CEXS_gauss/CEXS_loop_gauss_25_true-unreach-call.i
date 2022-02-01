extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
int main()
{
  //int IN;
  //__VERIFIER_assume(IN >= 50);

  int n = 325; // == 25 * 26 / 2

  int i = 0;
  int a = 0;

  while (a < n)
  {
        i++;
	a += i;
  }

  if(!(a == i*(i+1)/2))
    __VERIFIER_error();

  return 0;
}
