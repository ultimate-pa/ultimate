#include<stdlib.h>

void *malloc(size_t size);
int *p;

int copy_from_user();
int init(int a);
int f();

int state = 0;
void __VERIFIER_error();

int probe(void ) {
	int a, k, r;

	state = 1;
	a = copy_from_user();
	k = init(a);
	if(a+k<10) {
		goto err2;
	}
	
	r = f();
	if(!r) {
		goto err3;
	}

	return 0;

	err3:
		//non security
		//forgot state=0;
		return -1;
	err2:
		state=0;
		return -1;
}

void disconnect() {
 state=0;
}

void main() {
	if(probe()==0) {
		disconnect();
	}
	if(state!=0) __VERIFIER_error();
	
}
