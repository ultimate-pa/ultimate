//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2018-03-02
 *
 *
 */

extern int __VERIFIER_nondet_int(void);


int main() {
    // = __VERIFIER_nondet_uint();
    int *cakeLeft; // = __VERIFIER_nondet_uint();
    int *eat;
    *eat = *cakeLeft / 3;
    if (*cakeLeft >= 10000) {
        while(__VERIFIER_nondet_int()) {
            *cakeLeft = *cakeLeft - *eat;
            *eat = (*eat + 1) / 3;
        }
        if (cakeLeft != eat) {
            if (*cakeLeft < 10000) {
                //@ assert \false;
            }
        }
    }
    return 0;
}
