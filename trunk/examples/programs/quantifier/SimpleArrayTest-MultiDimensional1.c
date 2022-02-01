//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 27.7.2012
//
// example tests several things at one,
// should maybe splittet into several files

void procWithArray();

void procWithArray() {
	int i = 1;
	int oneDim0[10] = {1,2};
	int oneDim1[] = { 1 };
	oneDim0[2] = 3;

	oneDim0[1] = oneDim1[0];

	int a[1][2];
	a[0][1] = 0;

	int b[i][++i][i];
	b[0][--i][0] = 0;

	int test [4][2][2] = {
			{
					{3,1}, {4, 5}
			}, {
					{0} 
			}, {
					{8,9}
			}, {
					{10, 11}
			}
	};
}