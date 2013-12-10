//#Termination
/*
 * Program from Fig.1a of
 * 2009PLDI - Gulwani,Jain,Koskinen - Control-flow refinement and progress invariants for bound analysis
 *
 * Date: 9.12.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

int __VERIFIER_nondet_int() { int val; return val; }

void cyclic(int id, int maxId) {
    if(0 <= id && id < maxId) {
        int tmp = id+1;
        while(tmp!=id && __VERIFIER_nondet_int()) {
            if (tmp <= maxId) {
                tmp = tmp + 1;
            } else {
                tmp = 0;
            }
        }
    }
}

int main() {
	int id = __VERIFIER_nondet_int();
	int maxId = __VERIFIER_nondet_int();
	cyclic(id,maxId);
    return 0;
}


