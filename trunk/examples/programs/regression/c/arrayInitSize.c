// #Safe
/*
 * Date: 2025-12-12
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

int main(){
  int x[] = {1,2,3};
  if (sizeof(x) != 3 * sizeof(int)) reach_error();
  
  int y[5] = {1,2,3};
  if (sizeof(y) != 5 * sizeof(int)) reach_error();
}
