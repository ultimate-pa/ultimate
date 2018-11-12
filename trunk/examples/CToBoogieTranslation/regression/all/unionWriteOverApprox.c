//#Unknown
/*
 * Example to check that the overapproximation flag is correctly set
 * when a union field is assigned to and union fields of other types 
 * exist.
 */
int main() {
  union u {
    int x;
    float y;
  } un1;

  un1.y = 15.0;

  //@ assert un1.x != 0;
}
