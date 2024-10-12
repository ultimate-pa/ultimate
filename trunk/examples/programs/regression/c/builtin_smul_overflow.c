//#Safe
/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2024-07-02
 */

int main(){
  int r;
  __builtin_smul_overflow(-2147483647, 3, &r);
  //@ assert r == -2147483645;
  __builtin_smul_overflow(-2147483647, 6, &r);
  //@ assert r == 6;
}
