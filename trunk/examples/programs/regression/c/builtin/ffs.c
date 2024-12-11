// #Safe
/*
 * Date: December 2023
 * Author: Dominik Klumpp
 */
extern int __VERIFIER_nondet_int();
extern long __VERIFIER_nondet_long();
extern long long __VERIFIER_nondet_longlong();

#include <strings>

int main() {
    int i = __VERIFIER_nondet_int();
    int x = ffs(i);
    //@ assert x >= 0;
    //@ assert x <= 32;
    //@ assert (i == 0) == (x == 0);

    long l = __VERIFIER_nondet_long();
    int y = ffsl(l);
    //@ assert y >= 0;
    //@ assert y <= 32;
    //@ assert (l == 0) == (y == 0);

    long long ll = __VERIFIER_nondet_longlong();
    int z = ffsll(ll);
    //@ assert z >= 0;
    //@ assert z <= 64;
    //@ assert (ll == 0) == (z == 0);

    int a = ffs(4);
    // The following assert can probably only be proven in bit-precise mode.
    //@ assert a == 3;
}
