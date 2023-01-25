// #Safe
/*
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 28. 01. 2020
 */

#include <pthread.h>
#include <stdio.h>

typedef unsigned long int pthread_t;

_Bool search_found;
int search_result;
int search_needle;
int* search_haystack;

void* search_worker(void* params) {
  int* bounds = (int*) params;
  int lower = bounds[0];
  int upper = bounds[1];
  for (int i = lower; i < upper && !search_found; i++) {
    if (search_haystack[i] == search_needle) {
      search_found = 1;
      search_result = i;
    }
  }
  return NULL;
}

int search(int* haystack, int len, int needle) {
  pthread_t searcher1;
  pthread_t searcher2;
  pthread_t searcher3;

  search_found = 0;
  search_needle = needle;
  search_haystack = haystack;

  int bounds1[2] = {0, len/3};
  pthread_create(&searcher1, NULL, search_worker, (void*)bounds1);
  int bounds2[2] = {len/3, (2*len)/3};
  pthread_create(&searcher2, NULL, search_worker, (void*)bounds2);
  int bounds3[2] = {(2*len)/3, len};
  pthread_create(&searcher3, NULL, search_worker, (void*)bounds3);

  pthread_join(searcher1, NULL);
  pthread_join(searcher2, NULL);
  pthread_join(searcher3, NULL);

  if (search_found) {
    return search_result;
  } else {
    return -1;
  }
}


void main() {
  int len = __VERIFIER_nondet_int();
  int haystack[len];
  int needle = __VERIFIER_nondet_int();

  int pos = search(haystack, len, needle);
  if (pos == -1) {
    int i = __VERIFIER_nondet_int();
    __VERIFIER_assume(0 <= i && i < len);
    int val = haystack[i];
    // // -- assert val != needle; // needs quantified assertions
  } else {
    int val = haystack[pos];
    //@ assert val == needle;
  }

  free(haystack);
}
