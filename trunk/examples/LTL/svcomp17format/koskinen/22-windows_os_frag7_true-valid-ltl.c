// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

// Benchmark: win7.c
// Property: G F WItemsNum >= 1


extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int WItemsNum;

WItemsNum = __VERIFIER_nondet_int();

void callback1() {}
void callback2() {}
#define MoreWItems() __VERIFIER_nondet_int()

void main() {
    WItemsNum = __VERIFIER_nondet_int();
    while(1) {
        while(WItemsNum<=5 || MoreWItems()) {
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
