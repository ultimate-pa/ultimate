struct arrayStruct1 {
	int a[2];
	char b;
};

typedef struct {
	int ia[13];
	float c;
} arrayStruct2;

struct arrayStruct1 as1Glob;
arrayStruct2 as2Glob = { {1}, 1.0};

int main() {
	struct arrayStructLocal {
		int a[11];
		char b;
	} asl;

	asl.b = 'a';

	arrayStruct2 as2;
	as2.c = 1.0;

	struct arrayStruct1 as1;
	as1.a[0] = 1;
}
