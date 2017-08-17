//#termcomp16-someonesaidyes
/*
 * Modified variant of the program depicted in Fig.8a of
 * 2013TACAS - Cook,See,Zuleger - Ramsey vs. Lexicographic Termination Proving
 *
 * Date: 2014
 * Author: Caterina Urban
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int K, x;
    K = __VERIFIER_nondet_int();
    x = __VERIFIER_nondet_int();
    while (x != K) {
        if (x > K) {
            x = x - 1;
        } else {
            x = x + 1;
        }
    }
    return 0;
}
