//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Simple Program which is correct with respect to assertions.
 * In order to proof correctness one has to infer loop invariants e.g. x>=0
 *
 * The example is taken from our SAS'09 paper "Refinement of Trace Abstraction".
 * http://www.springerlink.com/content/d372357375t64146/fulltext.pdf
 *
 */


int nondet() {
    int x;
    return x;
}


int main() {
    int x, y;

    x = 0;
    y = 0;

    while (nondet()) {
        x = x + 1;
    }

    //@ assert x != -1;
    //@ assert y != -1;
    return 0;
}
