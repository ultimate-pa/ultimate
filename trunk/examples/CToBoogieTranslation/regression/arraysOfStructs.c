//#Safe
/*
 * author: nutz, 23.01.2014, updated with "Safe" annotation in Nov 2017
 */
int main() {

	struct structType {
		int a;
		int b;
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
	//@assert s2.x == 7;

	s1a[0].x = 9;
	s2a[1] = s1a[0];
	i = s2a[1].x;
	//@assert i == 9;
}
