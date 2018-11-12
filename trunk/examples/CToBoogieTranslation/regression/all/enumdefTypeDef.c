////#Safe
/*
 * author: nutz
 */

#include<stddef.h>

enum globE { a, b, c};


int main() {
  enum globE gei = c;
  gei = 9;

  enum aufz { null = 0, nix = 0, eins , zwei , drei , zehn = 10 , elf };
  typedef enum aufz aufz;

  enum enu { loewe, stier, hund };

  enum aufz a1;
  aufz a2;
  enum aufz a3 = drei;
  aufz a4 = elf;
  aufz a5 = hund;
 
  return 0;
}
