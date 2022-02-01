//#Unsafe
/*
 * 2020-04-11
 * Delta-debugged example from ldv-regression/rule60_list2.i
 * For IsEmptyHeuristic: AssertionError: IsEmptyHeuristic did not match IsEmpty
 * 
 * Author: dietsch@cs.uni-freiburg.de
 */

void __blast_assert()
{
 ERROR: __VERIFIER_error();
}

void * __getMemory(int size)
{

  if ( __VERIFIER_nondet_int())
 return 0;

}

void *my_malloc(int size) {
  return __getMemory(0);
}

void list_add(int  new, int  head) {
           __blast_assert () ;

}

void main() {
  int  dev1,  dev2;
      my_malloc(   0 );
  dev2 = my_malloc(   0 );
  if(    dev2  ) {
    list_add(0, 0);

  }

}

