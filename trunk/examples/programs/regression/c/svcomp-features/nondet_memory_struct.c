//#Safe
/*
 * Date: 2026-10-28
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

struct S {
    long x;
    int y;
};

int main()
{
    struct S s = { 1, 1 };
    __VERIFIER_nondet_memory(&s, sizeof(long));
    //@ assert s.y == 1;
}
