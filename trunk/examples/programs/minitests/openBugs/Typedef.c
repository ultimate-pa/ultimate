struct foo;
struct foo;
typedef struct foo TEST;
struct foo {
	int x;
	int y;
};

int main() {
	typedef int A;
	A a;
	a = 5;
	typedef struct foo B;
	B b = { 0, 0 };
	typedef TEST C;
	C c = { 1, 1 };
}
