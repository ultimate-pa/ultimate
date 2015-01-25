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

//#Unsafe
//Bug: Endlosschleife am Ende geloescht -> Property wird
//nicht mehr richtig gecheckt.
//@ ltl invariant positive: !AP(c > 5) || <>AP(resp > 5);
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int c;
int servers ;
int resp; //can never get > 4
int curr_serv;

  c = __VERIFIER_nondet_int();

  servers = 4;
  resp = 0;
  curr_serv = servers;

int main() {
  __VERIFIER_assume(c>0);
  while(curr_serv > 0) {
    if(__VERIFIER_nondet_int()) {
      c--; 
	  curr_serv--;
      resp++;
    } else {
	 __VERIFIER_assume(c < curr_serv);
      curr_serv--;
    }
  }
}

