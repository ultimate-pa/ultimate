//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-08-15
 *
 *
 */
#include <math.h>

extern float __VERIFIER_nondet_float(void);
extern int __VERIFIER_nondet_int(void);


int main() {
    float eat = __VERIFIER_nondet_float();
    float cakeLeft = __VERIFIER_nondet_float();
    if (eat <= cakeLeft / 2.0 && 0.0 <= cakeLeft && !isinf(cakeLeft)) {
        cakeLeft = cakeLeft - eat;
        eat = eat / 2.0;
        if (!(eat <= cakeLeft / 2.0 && cakeLeft >= 0.0)) {
            //@ assert \false;
        }
    }
    return 0;
}
