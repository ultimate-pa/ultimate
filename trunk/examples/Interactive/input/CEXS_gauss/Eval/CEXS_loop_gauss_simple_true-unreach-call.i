extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
int main()
{
  // Gauss example with {{loop_count}} iterations.
  int n = {{(loop_count*(loop_count+1)/2)|int}}; // == {{loop_count}} * {{loop_count+1}} / 2

  int i = 0;
  int a = 0;

  while (a < n)
  {
        i++;
	a += i;
  }

  if(!(i == {{loop_count}}))
    __VERIFIER_error();

  return 0;
}
