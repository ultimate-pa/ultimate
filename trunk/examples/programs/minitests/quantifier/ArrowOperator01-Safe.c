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
	int* i;
	int a = *i;
	fraction x = { 2, 5 };
//	int a = x.denom;
	x.denom = 7;
	fraction* p = malloc(sizeof(fraction));
//	fraction* p;
//	int a = p->num + 384;

}
