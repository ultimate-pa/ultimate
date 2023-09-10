//#Unsafe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-12-07
*/

extern int printk(char const * , ...);

int main() {
  int x = printk("%d, %d", 1, 2);
  //@ assert 0;
}