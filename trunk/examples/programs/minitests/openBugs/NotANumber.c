// FIXED : 16.9.2012 / ML
// Bug Reported by Markus via Skype:
// Not a numeral exception in SMT for int var = 'A'
//
//Date: 30. July 2012
//Author: Markus Lindenmann
//

int foo[2] = {1,2,3};
int main() {
 int bar[] = {};
 foo[3] = 10;
 int x = foo[0];
 char arr[] = {'a', 'b'};
 _Bool f = 5;
 _Bool a[] = {0,1};
 if(a[1]) {
 a[0] = 1;
 }
 //@ assert a[0] == 1;
}
