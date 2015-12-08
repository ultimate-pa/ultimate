#define MAX_INT 0x7fffffff
#define MAX_CHAR 0x7f

static int x; // this static modifier is supposed to be ignored!
typedef struct {
	int x;
	int y;
} structType;

void localPrimitives(int);
void localStructs(int);
void localArrays(int);

int main() {
	//@ assert x == 0;
	for (int i = 0; i < MAX_INT - 3; i++) {
		localPrimitives(i);
		localStructs(i);
		localArrays(i);
	}
}

static int foo(int i) {

}

void localStructs(int i) {
	static struct {
		int x;
		int y;
	} f;
	//@ assert f.x == 0;
	//@ assert f.y == 0;
	static struct {
		int x;
		int y;
	} g = { 2, 0 };
	//@ assert g.y == 0;
	//@ assert g.x == i + 2;
	g.x++;
	static structType d;
	//@ assert d.x == i;
	//@ assert d.y == i;
	d.x++;
	d.y++;
	static structType e = { 0, 1 };
	//@ assert e.x == i;
	//@ assert e.y == i + 1;
	e.x++;
	e.y++;
}

void localArrays(int i) {
	static int arr[10];
	for (int j = 0; j < 10; j++) {
		//@ assert arr[j] == i;
		arr[j]++;
	}
	static int arr1[2] = { 1, 1 };
	for (int j = 0; j < 2; j++) {
		//@ assert arr1[j] == i + 1;
		arr1[j]++;
	}
}

void localPrimitives(int i) {
	static int s; // auto initialized with 0;
	static int x = 1;
	//@ assert s == i;
	//@ assert x == i + 1;
	s++;
	x++;
	static int a, b = 3;
	//@ assert a == i;
	//@ assert b == i+3;
	a++;
	b++;
	static char l = 1, m = 2;
	if (i <= MAX_CHAR - 2) {
		//@ assert l == i + 1;
		//@ assert m == i + 2;
		l++;
		m++;
	}
}
