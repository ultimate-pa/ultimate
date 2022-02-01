//#Termination
/*
 * Program from Fig.1a of
 * 2009PLDI - Gulwani,Jain,Koskinen - Control-flow refinement and progress invariants for bound analysis
 *
 * Date: 9.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
    int id, maxId, tmp;
    id = __VERIFIER_nondet_int();
    maxId = __VERIFIER_nondet_int();


    if(0 <= id && id < maxId) {
        tmp = id+1;
        while(tmp!=id && __VERIFIER_nondet_int() != 0) {
            if (tmp <= maxId) {
                tmp = tmp + 1;
            } else {
                tmp = 0;
            }
        }
    }


    return 0;
}
