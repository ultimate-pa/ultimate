extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int a = 0;
int r = 0;

int main() {
   int n;
  while(__VERIFIER_nondet_int()) {
    a = 1;
    a = 0;
    n = __VERIFIER_nondet_int();
    while(n>0) {
      n--;
    }
    r = 1;
    r = 0;
  }
  return 0;
}
