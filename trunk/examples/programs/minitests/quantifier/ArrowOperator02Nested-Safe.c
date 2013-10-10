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

typedef struct {
      fraction frac;
} fstruct;

typedef struct {
      fraction* frac;
} pstruct;



int main() {
	int* i;
	int a = *i;
	fraction* p;
//	fstruct* fs;
	fstruct* ps;
	a = ps->frac->num;
	//@ assert a == 387;
}
