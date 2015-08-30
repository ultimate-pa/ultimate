//#Unsafe
/* According to 6.5.8.6 the behavior is undefined for the relational operator
 * below.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-08-30
 * 
 */

#include <stdlib.h>

int main() {
	int a[7];
	int b[7];
	int x = (&a > &b);
}
