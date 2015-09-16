//#Unsafe
/* 
 * Author: langt@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * Date: 24.08.2015
 */

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

int main() {
	/* bitwise complement */
	{
		int x = 5;
		int y = ~x;

        if (y != -5) {
          __VERIFIER_error();
        }
	}
}
