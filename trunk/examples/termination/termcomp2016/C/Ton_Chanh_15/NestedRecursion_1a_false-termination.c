//#termcomp16-someonesaidno
/*
 * Date: 06/07/2015
 * Created by: Ton Chanh Le (chanhle@comp.nus.edu.sg)
 * Adapted from AProVE_numeric/ex3.c
 */

extern int __VERIFIER_nondet_int();
int rec1(int i);
int rec2(int j);

int rec1(int i) {
  if(i <= 0)
    return 0;
  return rec1(rec1(rec1(i-2) - 1)) + 1;
}

int rec2(int j) {
  if(j <= 0)
    return 0;
  return rec2(rec1(j+1)) - 1;
}

int main() {
  int x = __VERIFIER_nondet_int();
  rec2(x);
}