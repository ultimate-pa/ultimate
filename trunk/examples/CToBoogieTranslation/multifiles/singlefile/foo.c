const int magic = 4;

int foo(int x) {
    return x + bar(x - 1);
}

int main() {
  return foo(42);
}

int bar(int y) {
    int w = 3;
    if (y < magic) {
        int z = 5;
        if (1) {
          int q = 3;
          int z = 2;
        }
        return z;
    }
    return y + foo(y) + w;
}
