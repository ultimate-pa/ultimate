extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));
int Stored;
void init() { Stored = 0; }
void callback() {}
void IoQueueWorkItem() {}
void main() {
    while(__VERIFIER_nondet_int()) {
           if (__VERIFIER_nondet_int()) {
               callback ();
           } else {
        IoQueueWorkItem ();
               Stored = 1;
               break;
           }
    }
    if (Stored==1) {
        callback ();
        Stored = 0;
    }
}
