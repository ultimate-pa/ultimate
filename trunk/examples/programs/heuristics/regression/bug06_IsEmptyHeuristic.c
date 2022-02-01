//#Unsafe
/*
 * 2020-04-17
 * Delta-debugged example from list-ext3-properties/sll_of_sll_nondet_append-2.i
 * For IsEmptyHeuristic: AssertionError: IsEmptyHeuristic did not match IsEmpty
 * 
 * Author: dietsch@cs.uni-freiburg.de
 */

void sll_create(int len) {

  while(len    ) {

    len--;
  }

}
void node_create_with_sublist(int sublist_length) {

      sll_create(sublist_length);

}

void sll_append(int  head, int sublist_length) {
    node_create_with_sublist(sublist_length);

}

void main() {

  int i, j;

  for(i = 0; i <= 1; i++) {
    for(;     __VERIFIER_nondet_int();  ) {
      sll_append(0, i);
    }
  }
  sll_append(0, 1);

 ERROR: __VERIFIER_error();

}


