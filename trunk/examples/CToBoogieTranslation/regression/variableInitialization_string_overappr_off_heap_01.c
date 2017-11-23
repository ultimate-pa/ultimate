//#Safe
/*
 * Program is safe but we don't expect to prove it correct because strings
 * with more than 7 characters are overapproximated.
 */
int main() {
  char s[] = "longenough";

  if (s[1] != 'o') {
    //@ assert \false;
  }
}
