//#Safe
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
	int *q = 0;
//	q = 0;
	int b = !q;
	//@ assert b != 0;
	if (!p || q) {
	  //@ assert \false;
	}
    free(p);
    return 0;
}
