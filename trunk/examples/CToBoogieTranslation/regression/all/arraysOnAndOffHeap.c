/*
 * author: nutz, 18.12.2013
 */

int ga[5], (*pga)[5];

int mdga[2][3][1];
int mdgaH[2][3], (*mdgaHp)[2][3];


int main() {
	int i[3], j, (*p)[3];
	p = &i; //forces onHeap for i
	j = i[2];
	i[0] = 1;
	i[1] = (*p)[2] + 4;


	mdga[1][2][0] = 4;
	j = mdga[1][2][0];

	mdgaHp = &mdgaH;
}
