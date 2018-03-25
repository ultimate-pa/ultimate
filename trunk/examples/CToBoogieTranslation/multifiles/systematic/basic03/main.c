#include "vardef.h"

int main()
{
  //@assert c == 7;
  addToC();
  //@assert c == 8;
  for (int i = 0; i < 10; i++) {
    //@assert c == 8 + i;
    addToC();
  }
  //@assert c == 18;
}
