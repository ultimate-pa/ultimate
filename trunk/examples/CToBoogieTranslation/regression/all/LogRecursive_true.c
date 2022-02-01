/*
 Do not use the log function from math.h if it is overwritten
*/

#include <math.h>

extern int __VERIFIER_nondet_int(void);
int log(int x, int y);
int random(void);

int main() {
	int x = __VERIFIER_nondet_int();
	if(x < 0)
		return 0;
	int y = __VERIFIER_nondet_int();
	if(y < 0) 
		return 0;
	int z = __VERIFIER_nondet_int();
	log(x,y);

}

int random() {
	int x = __VERIFIER_nondet_int();
	if (x < 0)
		return -x;
	else
		return x;
}

int log(int x, int y) {
    if (x >= y && y > 1) {
      return 1 + log(x/y, y);
    }
    return 0;
  }
