// PRIMITIVE =============================
int a, b, c, d = 10;
int e;
_Bool f;
_Bool g = 1;
char h = 'H';
char i;
float j = 3.0;
float k;
// ARRAYS ================================
int arr0[5];
int arr1[d][h];
typedef struct {
	int x;
	int y;
} foo;
foo arr2[10][20][30];
// STRUCTS ===============================
typedef struct {
	int nr, nr0;
	char c;
	_Bool b;
	foo test;
} struct0, struct1;
typedef struct abc {
	int a, b;
	char c;
	_Bool d;
	foo e[10];
} struct2, struct3, struct4;

struct element1 {
	struct2 a, b;
	struct0 e1[100];
	foo bar;
} struct5;

int main() {
	//@ assert a=0;
	//@ assert b=0;
	//@ assert c=0;
	//@ assert d=10;
	//@ assert e=0;
	//@ assert f=0;
	//@ assert g=1;
	//@ assert f=\false;
	//@ assert g=\true;
	//@ assert h!=0;
	//@ assert i=0;
	//@ assert j=3.0;
	//@ assert k=0.0;
	static int local_l;
	//@ assert local_l=0;
	int local_m;
	for (int i = 0; i < 5; i++) {
		//@ assert arr0[i] = 0;
	}
	for (int i = 0; i < d; i++) {
		for (int j = 0; j < h; j++) {
			//@ assert arr1[i][j]==0;
		}
	}
}
