/*
 * author: nutz, 27.01.2014
 */


int main() {

	struct structType {
		int a;
		int *b;
	};

	struct nestedStructType {
		int x;
		struct structType s;
	};

	struct nestedStructType s1, *s1p, s1a[3];
	struct nestedStructType s2, *s2p, s2a[4];

	int i;


	s1.x = 7;
	s2 = s1;
	s1 = s2;
//	//@assert s2.x == 7;

	s2p = &s2; //force s2 to be on Heap
}
