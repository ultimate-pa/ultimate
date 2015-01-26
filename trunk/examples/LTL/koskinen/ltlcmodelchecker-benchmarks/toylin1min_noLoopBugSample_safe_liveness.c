//#Safe
// *************************************************************
//
//     Branching-time reasoning for infinite-state systems
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// *************************************************************

// Benchmark: toylin1.c
// Property: c > 5 => AF(resp > 5)


//@ ltl invariant positive: !<>AP(c > 5);
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int curr_serv;
int c;
curr_serv = 3;
c = 0;

int main() {
  while(curr_serv > 0) {
	  curr_serv--;
	  c++; //can get > 3
  }
}

