// #Safe
/*
 * Date: 2024-11-15
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

struct s {
  int x;
  struct { int y; int z; };
};

int main(){
  struct s s1 = {1,2,3};
  struct s s2 = {1,{2,3}};
  //@ assert s1.x == s2.x;
  //@ assert s1.y == s2.y;
  //@ assert s1.z == s2.z;
}
