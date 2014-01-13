/* #Safe
 * Author: lindenmm@informatik.uni-freiburg.de
 * Date: 16.08.2012
 * contains examples from: http://www2.informatik.uni-halle.de/lehre/c/c_struct.html
 */

typedef int foo;

typedef struct {
	int nr, nr0;
	char c;
	_Bool b;
	foo test;
} element0, asf;

typedef struct abc {
	int a, b;
	char c;
	_Bool d;
	foo e;
} e1, e2, e3;

struct element1 {
	int a, b;
	element0 bar;
};

element0 c[10];
struct element1 d[2] = { { 1, 2, { 3, 4 } }, { 0, 0 } };
struct element1 e[2] = { { 0, 0, { 0, 0 } }, { 1, 1 } };

struct element2 {
	int a, b;
	element0 bar[2];
};

struct test1 {
	int a[10];
	int b;
};

struct element2 testWArray;

element0 globalStruct;

void test0(void) {
	// d = e; commented out by alex: C does not allow assignments between arrays
	d[0] = e[0];
	if (e[0].a != 0) {
		//@ assert \false;
	}
	asf acc0 = { .nr = 0 };
	asf acc1 = { .nr = 0, .nr0 = 1 };
	asf acc2 = { 3, 4 };
	asf acc3 = { .nr = 0, 1 };
	struct sfa {
		int bla;
	} test = { 3 };
	test.bla = 10;
	acc0.nr0 = 1;
	int i = acc0.nr0;
	//@ assert i == 1;
	struct element1 t = { .a = 1, .b = 2, .bar = { .nr = 5 } };
	struct element1 u = { 1, 2, .bar = { .nr = 5 } };
	struct element1 v = { 1, 2, { .nr = 5 } };
	t.bar.b = 1;
	testWArray.bar[0].nr = 10;
	i = t.bar.c;
	globalStruct.b = 0;
	if ((globalStruct.b)) {
		i++;
	}
	if (!(t.bar.b)) {
		i++;
	}
//	if (!(t.bar)) { // should be a type error!
//		i++;
//	}
//	if (d) { // should be a type error!
//		i++;
//	}
}

void test1Helper(int i) {

}

void test1(void) {
	struct test1 t1;
	t1.b = 0;
	test1Helper(t1.b++);
	test1Helper(++t1.b);
	t1.b--;
	--t1.b;
	if (t1.b != 0) {
		//@ assert \false;
	}
	t1.a[0] = 0;
	test1Helper(t1.a[0]++);
	test1Helper(++t1.a[0]);
	t1.a[0]--;
	--t1.a[0];
	if (t1.a[0] != 0) {
		//@ assert \false;
	}
	int x = 10;
	int xOld = x;
	x += t1.b;
	//@ assert x == t1.b + xOld;

	struct test1 t2[10];
	t2[0].b = 0;
	test1Helper(t2[0].b++);
	test1Helper(++t2[0].b);
	t2[0].b--;
	--t2[0].b;
	if (t2[0].b != 0) {
		//@ assert \false;
	}
	t2[0].a[0] = 0;
	t2[0].a[0]++;
	++t2[0].a[0];
	t2[0].a[0]--;
	--t2[0].a[0];
	if (t2[0].a[0] != 0) {
		//@ assert \false;
	}
	x = 10;
	xOld = x;
	x += t2[0].b;
	if (x != t2[0].b + xOld) {
		//@ assert \false;
	}
}

int main() {
	test0();
	test1();
	struct person { /* deklariert den Strukturtyp person */
		int alter;
		float gewicht;
		char name[25];
	} adam, eva; /* deklariert Variable des Typs person */

	struct person paul; /* deklariert weitere Variable des Typs person */

	paul.alter = 13; /* Zuweisung von Werten an die */
	paul.gewicht = 47.8; /* einzelnen Komponenten */

	struct point /* deklariert den Strukturtyp point */
	{
		int x;
		int y;
	} pkt0 = { 20, 40 }; /* definiert die Variable pkt1 und initialisiert
	 ihre beiden Felder (x = 20, y = 40) */
	struct point pkt1 = { 2, 3 };
	struct point pkt2;
	pkt2 = pkt1;
}

struct complx {
	double re;
	double im;
};

struct complx init(double r, double i) {
	struct complx new;
	new.re = r;
	new.im = i;
	return new;
}

struct complx add(struct complx a, struct complx b) {
	struct complx c;
	c.re = a.re + b.re;
	c.im = a.im + b.im;
	return c;
}

struct complx mult(struct complx a, struct complx b) {
	struct complx c;
	c.re = a.re * b.re - a.im * b.im;
	c.im = a.re * b.im + a.im * b.re;
	return c;
}
