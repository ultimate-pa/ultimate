//#Safe
/*
 * Program obtained by the program transformation which the Ramsey based
 * TERMINATOR uses to prove that the loop
 * while (x>0 && y>0) {if(*){x--} else {x=*;y--}}
 * has the transition invariant y'<y \/ x'<x.
 *
 * Progam  in Fig.3 of 
 * 2013TACAS - Cook,See,Zuleger - Ramsey vs. Lexicographic Termination Proving
 *
 * Date: 21.3.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);

int main() {
    int copied = 0;
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    int oldx = __VERIFIER_nondet_int();
    int oldy = __VERIFIER_nondet_int();
    while (x>0 && y>0) {
        if (copied == 1) {
            //@ assert ( (x<oldx && 0<=oldx) || (y<oldy && 0<=oldy));
        } else {
            if (__VERIFIER_nondet_int()) {
                copied = 1;
                oldx = x;
                oldy = y;
            }
        }
        
        if (__VERIFIER_nondet_int()) {
            x = x -1;
        } else {
            x = __VERIFIER_nondet_int();
            y = y -1;
        }
    }
}