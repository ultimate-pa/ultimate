#define MAX_INT 0x7fffffff
#define MAX_CHAR 0x7f

static int x; // this static modifier is supposed to be ignored!
typedef struct {
	int x;
	int y;
} structType;

void localPrimitives(int);

int main() {
	//@ assert x == 0;
	for (int i = 0; i < 3; i++) {
		localPrimitives(i);
	}
}

static int foo(int i) {

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
