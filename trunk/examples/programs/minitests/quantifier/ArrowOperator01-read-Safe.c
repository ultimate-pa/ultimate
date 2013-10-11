//#iSafe
/*
 * Date: October 2013
 * Author: Christian Schilling and heizmann@informtik.uni-freiburg.de
 * 
 */

typedef struct {
	int num;
	int denom;
} fraction;

int main() {
	fraction* p;
	int a;
	a = p->num;
	int b;
	b = (*p).num;
	//@ assert a == b;
}
