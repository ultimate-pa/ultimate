//#Safe

typedef struct { int x; } DATA;
typedef struct { DATA d; } RESULT;

int main() {
  DATA data;
  data.x = 42;
  RESULT result = { .d = data };
  //@ assert result.d.x == 42;
}

