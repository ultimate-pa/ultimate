//#Safe
/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-07-02
 */

int main(){
  int r;
  _Bool overflow = __builtin_umul_overflow(2147483647, 3, &r);
  //@ assert overflow;
  //@ assert r == 2147483645;
}
