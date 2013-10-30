//#iSafe
/*
 * Date: October 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

int main() {
    int *p = malloc(sizeof(int));
	int a;
	a = !p;
	//@ assert a == 0;
    free(p);
    return 0;
}
