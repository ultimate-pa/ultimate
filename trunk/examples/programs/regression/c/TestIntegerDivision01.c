//#Safe
// Author: heizmann@informatik.uni-freiburg.de, Daniel Dietsch
// Date: 15.12.2014
// Integer division in C.

int main() {
   int divRes;
   int modRes;
   
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
   return 0;
}