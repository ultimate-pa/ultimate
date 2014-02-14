// #Safe
/*
 * Variable i of ACSL loop invariant occurs in two diffent scopes.
 * We have to translated this to Boogie program where loop invariant uses "the
 * inner i".
 * 
 * Note that this example is related to 
 * programs/toy/interpolationHostileLoop.bpl
 * if we replace the "10" in the loop condition by a big number the Automizer
 * is (at the moment) not able to prove correctness.
 * 
 * Date: 12.02.2013
 * Author: Markus Lindenmann and heizmann@informatik.uni-freiburg.de
 */

int main();

int main() {
    int i = -5;

    //@ loop invariant i >= 0;
    for (int i=0,x=0; i<10; i++) {
        x += i;
    }
    //@ assert i == -5;

}