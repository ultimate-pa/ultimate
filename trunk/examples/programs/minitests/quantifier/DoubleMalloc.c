//#iSafe
/*
 * Date: September 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

int main() {
    int *p = malloc(sizeof(int));
//    int *q = malloc(sizeof(int));
    p = 3;
//    q = 5;
	free(p);
//	free(q);
    return 0;
}
