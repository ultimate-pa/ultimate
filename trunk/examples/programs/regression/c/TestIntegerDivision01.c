//#Safe
// Author: heizmann@informatik.uni-freiburg.de, Daniel Dietsch
// Date: 15.12.2014
// Integer division in C.

#include <stdio.h>

int main() {
   int divident;
   int divRes;
   int modRes;
   
   /*
    * Test for Alex' integer literal preprocessing.
    */
   divRes = 32 / 13;
   modRes = 32 % 13;
   printf("%d",divRes);
   printf("%d",modRes);
   //@ assert divRes == 2;
   //@ assert modRes == 6;
   
   divRes = 32 / -13;
   modRes = 32 % -13;
   printf("%d",divRes);
   printf("%d",modRes);
   //@ assert divRes == -2;
   //@ assert modRes == 6;
   
   divRes = -32 / 13;
   modRes = -32 % 13;
   printf("%d",divRes);
   printf("%d",modRes);
   //@ assert divRes == -2;
   //@ assert modRes == -6;
   
   divRes = -32 / -13;
   modRes = -32 % -13;
   printf("%d",divRes);
   printf("%d",modRes);
   //@ assert divRes == 2;
   //@ assert modRes == -6;

   
   divRes = 32 / 16;
   modRes = 32 % 16;
   printf("%d",divRes);
   printf("%d",modRes);
   //@ assert divRes == 2;
   //@ assert modRes == 0;
   
   divRes = 32 / -16;
   modRes = 32 % -16;
   printf("%d",divRes);
   printf("%d",modRes);
   //@ assert divRes == -2;
   //@ assert modRes == 0;
   
   divRes = -32 / 16;
   modRes = -32 % 16;
   printf("%d",divRes);
   printf("%d",modRes);
   //@ assert divRes == -2;
   //@ assert modRes == 0;
   
   divRes = -32 / -16;
   modRes = -32 % -16;
   printf("%d",divRes);
   printf("%d",modRes);
   //@ assert divRes == 2;
   //@ assert modRes == 0;
   
   
   /*
    * Test for division translated to Boogie
    */
   divident = 32;   
   divRes = divident / 13;
   modRes = divident % 13;
   printf("%d",divRes);
   printf("%d",modRes);
   //@ assert divRes == 2;
   //@ assert modRes == 6;

   divident = 32;
   divRes = divident / -13;
   modRes = divident % -13;
   printf("%d",divRes);
   printf("%d",modRes);
   //@ assert divRes == -2;
   //@ assert modRes == 6;
   
   divident = -32;
   divRes = divident / 13;
   modRes = divident % 13;
   printf("%d",divRes);
   printf("%d",modRes);
   //@ assert divRes == -2;
   //@ assert modRes == -6;
   
   divident = -32;
   divRes = divident / -13;
   modRes = divident % -13;
   printf("%d",divRes);
   printf("%d",modRes);
   //@ assert divRes == 2;
   //@ assert modRes == -6;
   
   
   divident = 32;
   divRes = divident / 16;
   modRes = divident % 16;
   printf("%d",divRes);
   printf("%d",modRes);
   //@ assert divRes == 2;
   //@ assert modRes == 0;
   
   divident = 32;
   divRes = divident / -16;
   modRes = divident % -16;
   printf("%d",divRes);
   printf("%d",modRes);
   //@ assert divRes == -2;
   //@ assert modRes == 0;
   
   divident = -32;
   divRes = divident / 16;
   modRes = divident % 16;
   printf("%d",divRes);
   printf("%d",modRes);
   //@ assert divRes == -2;
   //@ assert modRes == 0;
   
   divident = -32;
   divRes = divident / -16;
   modRes = divident % -16;
   printf("%d",divRes);
   printf("%d",modRes);
   //@ assert divRes == 2;
   //@ assert modRes == 0;
     
   return 0;
}
