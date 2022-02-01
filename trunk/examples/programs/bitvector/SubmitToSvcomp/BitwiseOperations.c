//#Safe
/* 
 * Author: langt@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * Date: 24.08.2015
 */

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
	/* bitwise complement */
	{
		int x = 0;
		int y = ~x;

        if (y != -1) {
          __VERIFIER_error();
        }
	}

    /* left shift */
    {
        int x = 2;
        int y = x << 2;

        if (y != 8) {
          __VERIFIER_error();
        }
    }

    /* unsigned right shift */
    {
        unsigned int x = 16U;
        unsigned int y = x >> 2U;
        if (y != 4U) {
          __VERIFIER_error();
        }
    }

    /* signed right shift */
    {
        int x = 16;
        int y = x >> 2;

        if (y != 4) {
          __VERIFIER_error();
        }
    }
}
