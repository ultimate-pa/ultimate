//#Safe
int i;
int main() {
  i; // necessary to not trigger a bug in our ACSL handling (Nov 17)
  //@ assert i == 0;
}
