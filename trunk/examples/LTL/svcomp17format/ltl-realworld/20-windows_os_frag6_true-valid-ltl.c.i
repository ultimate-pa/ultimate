extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));
extern unsigned int __VERIFIER_nondet_unsigned() __attribute__ ((__noreturn__));
unsigned int WItemsNum;
int __INITIALIZED = 0;
void env_init() {
 WItemsNum = __VERIFIER_nondet_unsigned();
 __INITIALIZED = 1;
}
void callback1() {}
void callback2() {}
int main() {
    env_init();
    WItemsNum = __VERIFIER_nondet_unsigned();
    while(1) {
        while(WItemsNum<=5 || __VERIFIER_nondet_unsigned()) {
               if (WItemsNum<=5) {
                   callback1();
                   WItemsNum++;
               } else {
                   WItemsNum++;
               }
        }
        while(WItemsNum>2) {
             callback2();
             WItemsNum--;
        }
    }
    while(1) {}
}
