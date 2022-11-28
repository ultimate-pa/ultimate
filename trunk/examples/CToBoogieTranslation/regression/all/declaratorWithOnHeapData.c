//#Safe

int x;

int main() {
  // make sure x is on-heap
  int* p = &x;
  *p = 3;

  // declarator where the value of x has to be read from the heap
  char str[x];

  str[1] = 'a';
  char c = str[1];
  //@ assert c == 97;
}
