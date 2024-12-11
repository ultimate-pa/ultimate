//#Safe
/*
 * 2017-07-03: "unknown symbol ((_ to_fp 8 24) RoundingMode Real (_ FloatingPoint 8 24))" 
 *
 * Reported by Philipp Berger
 */


int x0;
int x1;
float x2;

int main() {
    x0 = 0;
    x2 = 0.01F;
    if (!x2) {
        ;
    }
    x1 = 0;
    for (;;)
        if (x0)
            __VERIFIER_error();
}
