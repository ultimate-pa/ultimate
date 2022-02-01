//#termcomp16-someonesaidno
/*
 * Date: 07/07/2015
 * Created by: Ton Chanh Le (chanhle@comp.nus.edu.sg)
 */

extern int __VERIFIER_nondet_int();

int bsearch(int i, int j)
{
  if (i>=j) return i;
  int mid = (i+j)/2;
  if (__VERIFIER_nondet_int()) 
    return bsearch(i,mid);
  return bsearch(mid+1,j);
}


int main() {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  bsearch(x, y);
}