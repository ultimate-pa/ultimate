// October 2013
// Matthias Heizmann
// static struct structType* not treated as static

typedef struct {
	int x;
	int y;
} structType;

void localPrimitives(int);

int main() {
	for (int i = 0; i < 3; i++) {
		localPrimitives(i);
		
	}
}



void localPrimitives(int i) {
	static int s; // auto initialized with 0;
	static int x = 1;
	static struct structType* p = 0;
	if (i > 0) {
	  if (p == 0) {
		//@ assert \false;
	  }
	}
//	p = malloc(sizeof(struct structType));
	//@ assert s == i;
	//@ assert x == i + 1;
	s++;
	x++;
	p++;
}
