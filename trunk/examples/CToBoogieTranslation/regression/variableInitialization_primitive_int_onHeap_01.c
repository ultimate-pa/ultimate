//#Unsafe
int main() {
  int i;
  &i;
  //@ assert i == 0;
}
