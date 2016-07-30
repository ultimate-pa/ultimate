extern void __VERIFIER_assume(int);
#include <math.h>
extern void __VERIFIER_error(void);
int main()
{
  double d, q, r;
  __VERIFIER_assume(isfinite(q));
  d=q;
  r=d+0;
  if(!(r==d)) __VERIFIER_error();
}
