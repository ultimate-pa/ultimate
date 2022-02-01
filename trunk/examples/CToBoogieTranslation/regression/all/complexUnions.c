//#Safe
/*
 * author: nutz, 10.02.2014
 */

union u {
	int ux;
	int *up;
};

typedef union v {
	int vx;
	int *vp;
} intPtrPair;

typedef union {
	intPtrPair ipp;
	struct st { 
		int i;
	       	int *p;
	} stru;
} complexUnion;

int main() {
	union u ui = { 9 };
	ui.ux = 4;
	intPtrPair ipp1, *ippp;
        ippp = malloc(sizeof(intPtrPair));
	ipp1.vx = ui.ux;
	//@assert ipp1.vx == 4;

	int *i = malloc(sizeof(int));;
	*i = 83;
	ipp1.vp = i;
	int j = *(ipp1.vp);
	//@assert j == 83;

	*i = 84;
	ippp->vp = i;
	*(ippp->vp) = *i;
	j = *(ippp->vp);
	i = ippp->vp;
	//@assert j == 84;

	complexUnion cu = { { 73 } };
	complexUnion cu2 = { ipp : { 74 } };
	complexUnion cu3 = { stru : { 75 } };
	complexUnion cu4 = { stru : { 76, 0 } };
	cu.ipp.vx = j;
	cu.ipp.vp = i;
	cu.stru.i = j;
	*(cu.stru.p) = j;
	ui.ux = cu.stru.i;
}


