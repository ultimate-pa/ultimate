////#Safe
/*
 * Problem: the size of a variable length array depends on the value some variable
 * had at the time of initialization. We need to store this value inside a special 
 * auxiliary variable otherwise sa will get a wrong value in the example below.
 * author: nutz, 18.7.2014
 */

#include<stddef.h>
extern int __VERIFIER_nondet_int(void);

int f(long int a[]) {
 return 0;
}

int main() {
 int n = __VERIFIER_nondet_int();

 int soi = sizeof(int);
 
 int i;
 i = 0;
 int a[n];
 n = 0; 
 int sa = sizeof(a);
 //@ assert sa = n * soi;

 f(a); //force a to be on heap
 return 0;
}
