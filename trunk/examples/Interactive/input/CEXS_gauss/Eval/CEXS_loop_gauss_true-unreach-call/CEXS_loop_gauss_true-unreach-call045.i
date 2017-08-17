extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
int main()
{
  // Gauss example with 45 iterations.
  int n = 1035; // == 45 * 46 / 2

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