//#iSafe
/*
 * Date: October 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */
typedef struct {
      *fraction frac;
} pstruct;

typedef struct {
      fraction frac;
} fstruct;

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
//	fraction* p = malloc(sizeof(fraction));
	fraction* p;
	fstruct* fs;
	pstruct* ps;
	fraction f;
	
	p->num = 3;
	(*p).num = 3;
	
	f.frac.num = 3
	fs->frac.num = 3;
	ps->frac->num = 3;
// 	if ( (*p).num == 3) {
// 		a = p->num + 384;
// 		//@ assert a == 387;
// 	}
	

}
