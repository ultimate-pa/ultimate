//#Safe
/*
 * 2017-11-20 DD
 * 
 * Old Vars have to be assigned even if they are only read 
 *
 */

int SIZE;
int foo(int x) {
  int j=0;
  while (j<1) {
    j++;
  }
  if (j<SIZE) return 0;
  else return 1;
}
void main() {
  SIZE=2;

  if(foo(0)){
    __VERIFIER_error();
  }
}
