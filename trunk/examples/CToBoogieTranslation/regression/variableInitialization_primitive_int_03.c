//#Safe
int i = 1;
int main() {
  i; // necessary to not trigger a bug in our ACSL handling (as of Nov 17)
  //@ assert i == 1;
}
