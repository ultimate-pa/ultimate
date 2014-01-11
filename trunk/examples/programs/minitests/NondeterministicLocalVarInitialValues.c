/* #Unsafe
 * 
 * Local variables are not initialized. We may not assume that we obtain that
 * the same initial value in a in each iteration.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 12.10.2013
 * 
 */

int main() {
	int x = 0;
	int i = 0;
	while (i<2) {
		int a;
		if (i == 0) {
			x = a;
		} else {
			//@ assert x == a;
		}
		i++;
	}
}
