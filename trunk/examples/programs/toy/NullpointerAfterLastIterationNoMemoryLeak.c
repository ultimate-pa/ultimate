//#Safe
/*
 * Variant of Goanna example where x is not initialized, but there is no
 * memory leak.
 * 
 * Date: September 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

int main() {
    int x, *a;
    int *p = malloc(sizeof(int));
    if (x > 0) {
    	while ( x > 0 ) {
    		a = p;
    		if (x == 1) {
    			free(p);
    		}
    		x--;
    	}
    } else {
    	free(p);
    }
    return 0;
}
