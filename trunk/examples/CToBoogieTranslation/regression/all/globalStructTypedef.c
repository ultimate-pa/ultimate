struct struct1 {
	int a;
} struct1instance;

typedef struct struct1 struct2;

int main() {
	struct2 s;
	s.a = 5;
}
