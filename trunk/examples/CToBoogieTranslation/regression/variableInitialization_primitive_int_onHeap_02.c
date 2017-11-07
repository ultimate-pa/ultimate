//#Safe
int main() {
  int i = 1;
  &i;
  //@ assert i == 1;
}
