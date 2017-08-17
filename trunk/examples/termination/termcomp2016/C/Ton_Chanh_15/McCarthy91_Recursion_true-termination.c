//#termcomp16-someonesaidyes
/*
 * Date: 07/07/2015
 * Created by: Ton Chanh Le (chanhle@comp.nus.edu.sg)
 */

extern int __VERIFIER_nondet_int();

int mc91(int n)
{
  if (n > 100) return n-10;
  else return mc91(mc91(n+11));
}

int main() {
  int x = __VERIFIER_nondet_int();
  mc91(x);
}