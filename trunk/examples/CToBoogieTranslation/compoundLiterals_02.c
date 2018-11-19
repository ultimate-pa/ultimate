//#Safe
/*
 *
 * Test compound literals.
 *
 * C11 6.5.2.5.15 :
 * "Each compound literal creates only a single object in a given scope
 *  [..]
 * The function f() always returns the value 1."
 *
 * Here this means that the memory that compound literal "((struct s) { j++ })"
 * inhabits the same memory block in each iteration. However, that memory is
 * also overwritten in each iteration. In the second iteration, q stores the
 * compound literal's address, from the assignment "q = p" in the first
 * iteration.
 *
 * Also note 
 * C11 6.5.2.5.15 :
 * "Note that if an iteration statement were used instead of an explicit goto
 * and a labeled statement, the lifetime of the unnamed object would be the
 * body of the loop only, and on entry next time around p would have an
 * indeterminate value, which would result in undefined behavior."
 */
struct s { int i; };

int f (void)
{
  struct s *p = 0, *q;
  int j = 0;
  again:
    q = p, p = &((struct s) { j++ });
    if (j < 2) goto again;
    return p == q && q->i == 1;
}

int main() {
  int res;
  res = f();
  //@ assert res == 1;
}
