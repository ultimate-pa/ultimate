const int magic = 4;

int foo(int x) {
    return x + bar(x - 1);
}

int main() {
  return foo(42);
}

int bar(int y) {
    if (y < magic) {
        return 0;
    }
    return y + foo(y);
}
