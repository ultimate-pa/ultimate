/*
 * make use of all kinds of auxiliary variables in the translation
 * --> are they havoced correctly??
 * author: nutz, 18.02.2014
 */

union u {
	int ux;
	int *up;
};

//global array initialization on/off heap
int ga[4] = {1, 2};
int gaH[4] = {7, 8};

int main() {
	int (*arp)[4] = &gaH;


	//union: auxvars for havocing and initialization 
	union u ui = { 9 };
	ui.ux = 4;

	//pointer: auxvars for read and write operations on the heap
	int *p;
	*p = 9;
	ui.ux = *p;

	//increment/decrement operations
	int i;
	i++;
	i--;
	++i;
	--i;

	//local array initialization on/offHeap
	int a[4] = {1, 2};
	int aH[4] = {3, 4};

	arp = &aH;

	//struct initialization
	struct st {
		int a;
		int *p;
	} s = { *p, p } ;


}


