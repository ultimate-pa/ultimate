//#Safe

int x;

int main() {
  // make sure x is on-heap
  int* p = &x;
  *p = 3;

  // sizeof() requires fetching the value of x from the heap
  int y = sizeof(char[x]);

  //@ assert y == 3;
}
