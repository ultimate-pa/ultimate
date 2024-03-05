// #Safe
/*
 * Comparison of array (x) and pointer (y)
 * This is currently not correctly handled and leads to an exception:
 * TypeCheckException: [int]int is not unifiable to { base:int, offset:int }
 * 
 * Date: 2023-10-06
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

int x[2] = {1,2};

int main(){
  int* y = malloc(sizeof(int));
  if (x == y) reach_error();
}
