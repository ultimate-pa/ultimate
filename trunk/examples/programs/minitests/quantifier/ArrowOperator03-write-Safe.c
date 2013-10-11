//#iSafe
/*
 * Date: October 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

typedef struct {
	int num;
	int denom;
} fraction;

int main() {
	fraction* p;
	p->num = 3;
	(*p).denom = 4;
	int a = p->denom;
	//@ assert a == 4;
	int b = (*p).num;
	//@ assert b == 3;
}
