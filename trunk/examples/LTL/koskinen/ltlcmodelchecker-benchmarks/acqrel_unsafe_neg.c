//#Unsafe
// *************************************************************
//
//     Branching-time reasoning for infinite-state systems
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// *************************************************************

// Benchmark: acqrel.c
// Property: AG(a => AF r)
 

//@ ltl invariant positive: ![]( ! AP(a == 0) || <> AP(r == 0));
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int a = 0;
int r = 0;

int main() {
  int n;
  while(__VERIFIER_nondet_int() == 1) {
    a = 1;
    a = 0;
    n = __VERIFIER_nondet_int();
    while(n>0) {
      n--;
    }
    r = 1;
    r = 0;
  }
  while(1) { int x; x=x; }
  return 0;
}