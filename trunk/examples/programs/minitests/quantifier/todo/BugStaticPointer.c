// October 2013
// Matthias Heizmann
// static struct structType* not treated as static

struct structType{
	int x;
	int y;
};

void localPrimitives(int);

int main() {
	for (int i = 0; i < 3; i++) {
		localPrimitives(i);
		
	}
}

static int foo(static int i) {

}


void localPrimitives(int i) {
	static int s; // auto initialized with 0;
	static int x = 1;
	static struct structType* p = 0;
	if (i > 0) {
		*p = 3;
	}
	p = malloc(sizeof(struct structType));
	//@ assert s == i;
	//@ assert x == i + 1;
	s++;
	x++;
}
