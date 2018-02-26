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
    if (eat <= cakeLeft / 3.0 && 0.0 <= cakeLeft && !isinf(cakeLeft)) {
        cakeLeft = cakeLeft - eat;
        eat = eat / 3.0;
        if (!(eat <= cakeLeft / 3.0)) {
            //@ assert \false;
        }
    }
    return 0;
}
