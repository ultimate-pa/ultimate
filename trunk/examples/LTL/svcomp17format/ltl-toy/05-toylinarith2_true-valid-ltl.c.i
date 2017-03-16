extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));
unsigned int c ;
int servers ;
int resp;
int curr_serv;
int serversdiv2 ;
int __INITIALIZED = 0;
void env_init() {
 c = __VERIFIER_nondet_int();
 servers = __VERIFIER_nondet_int();
 serversdiv2 = __VERIFIER_nondet_int();
 __INITIALIZED = 1;
}
int main() {
 env_init();
 __VERIFIER_assume(servers>0 && c > 0);
 if(__VERIFIER_nondet_int())
  __VERIFIER_assume(serversdiv2+serversdiv2==servers);
 else
  __VERIFIER_assume(serversdiv2+serversdiv2+1==servers);
 resp = 0;
 curr_serv = servers;
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
