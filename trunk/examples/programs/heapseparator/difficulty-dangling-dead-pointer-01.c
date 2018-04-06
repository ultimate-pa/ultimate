/**
 * Currently (09.01.2018), the heap separator cannot separate the memory array 
 * in this example, although there is a semantics-preserving separation.
 *  (partition would be {{p}, {q,r}})
 * Combination of triggers for this problem:
 *  - r is used to access the memory array, thus it is taken into account for 
 *   partitioning.
 *  - r has a nondeterministic value at the positions where p and q are 
 *   dereferenced, it dangles between the potential partition blocks so to say, 
 *   and thus triggers their unification.
 */
int * nondet() {
  int *i;
  return i;
}

int main() {

  int *p = malloc(sizeof(int));
  int *q = malloc(sizeof(int));

  // initialize memory at p, q
  *p = 0;
  *q = 0;


  int *r = q;
  int z = *r;
  r = nondet();

  int x = *p;
  int y = *q;

  free(p);
  free(q);
}
