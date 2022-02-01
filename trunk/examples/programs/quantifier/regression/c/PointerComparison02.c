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
	int *p = malloc(4*sizeof(int));
	int *q = malloc(4*sizeof(int));
	int x = (p > q);
}
