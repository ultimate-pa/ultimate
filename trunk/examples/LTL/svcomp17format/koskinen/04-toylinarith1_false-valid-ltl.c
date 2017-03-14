// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************
//
// Benchmark: toylin1.c
// Property: c > 5 => F(resp > 5)
//
// DD: Koskinen said this was safe, but it is not.


extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int c;
int servers ;
int resp;
int curr_serv;


c = __VERIFIER_nondet_int(); 
servers = 4;
resp = 0;
curr_serv = servers;


int main() {
__VERIFIER_assume(c>0);
  while(curr_serv > 0) {
    if(__VERIFIER_nondet_int()) {
      c--; curr_serv--;
      resp++;
    } else {
      __VERIFIER_assume(c < curr_serv);
      curr_serv--;
    }
  }
  while(1) { int ddd; ddd=ddd; }
}

