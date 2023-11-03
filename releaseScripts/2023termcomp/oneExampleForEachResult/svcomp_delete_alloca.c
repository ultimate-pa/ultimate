#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int main() {
    int length1 = __VERIFIER_nondet_int();
    if (length1 < 1) {
        length1 = 1;
    }
    char* x = (char*) alloca(length1 * sizeof(char));
    char *y;
    if (x <= y && y < x + length1 * sizeof(char)) {
        *y = 0;
        while (*x != 0) {
            *x = 0;
            x++;
	    }
    }
    return 0;
}
