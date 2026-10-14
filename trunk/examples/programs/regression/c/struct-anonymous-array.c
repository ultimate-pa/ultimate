// #Safe
/*-----------------------------------------------------------------------------
 * Arrays inside an anonymous struct member, including verification of the
 * offset of the anonymous member via pointer arithmetic.
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 14.10.2026
 *---------------------------------------------------------------------------*/

struct s {
  int a;
  struct { int arr[3]; int b; };
};

int main(){
  struct s s1;
  s1.a = 1;
  s1.arr[0] = 10;
  s1.arr[1] = 20;
  s1.arr[2] = 30;
  s1.b = 4;
  //@ assert s1.a == 1;
  //@ assert s1.arr[0] == 10;
  //@ assert s1.arr[1] == 20;
  //@ assert s1.arr[2] == 30;
  //@ assert s1.b == 4;

  // offset check (anonymous member starts directly after a)
  int *p = &s1.arr[0];
  int *q = &s1.a + 1;
  //@ assert p == q;
  return 0;
}
