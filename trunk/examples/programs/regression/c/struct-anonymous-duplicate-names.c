// #Unsafe
/*-----------------------------------------------------------------------------
 * Duplicate member names across two anonymous members of the same struct.
 * This violates the uniqueness constraint of C11 6.7.2.1p15, so the program
 * is not valid C and the assertion is checked on an ill-formed program.
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 14.10.2026
 *---------------------------------------------------------------------------*/

struct s {
  struct { int x; };
  struct { int x; };
};

int main(){
  struct s s1;
  s1.x = 1;
  //@ assert s1.x == 1;
  return 0;
}
