//#Safe

int ask(int (*fn)(int));
int answer(int q);

int main() {
  int response = ask(&answer);
  //@ assert response == 42;
}

int ask(int (*fn)(int)) {
  return fn((int)&fn);
}

int answer(int q) {
  return 42;
}

