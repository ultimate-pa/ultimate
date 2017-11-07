//#Safe
int i = 1;
int main() {
  &i;
  //@ assert i == 1;
}
