//#Unsafe
/*
 * Date: 2026-10-28
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

int main()
{
    int x = 0;
    __VERIFIER_nondet_memory(&x, sizeof(int));
    //@ assert x < 256;
}
