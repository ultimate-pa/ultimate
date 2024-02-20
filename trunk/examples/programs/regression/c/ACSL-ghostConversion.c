// #Safe
/*
 * Test the conversion from int to long long for ghost variables.
 * 
 * Date: 2024-02-20
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

//@ ghost long long g = 0;

int main() {
  //@ ghost long long local = 1;
  //@ ghost g = 1;
  //@ assert g == local;
}
