/*
 * Date: 2014-06-08
 * Author: leike@informatik.uni-freiburg.de
 * Update: 2014-10-31
 *
 * This is Example 2.6 from the test suit used in
 *
 * Termination Proofs for Linear Simple Loops.
 * Hong Yi Chen, Shaked Flur, and Supratik Mukhopadhyay.
 * SAS 2012.
 * 
 * The authors of the paper claim that this program is terminating,
 * however the program only terminates over the integers and the rationals,
 * not over the reals.
 *
 * There is an infinite execution staring with the eigenvector
 * x = (sqrt(17) - 1) / 4
 * y = 1
 * with eigenvalue sqrt(17) - 1.
 *
 * The example was previously incorrectly classified.
 *
 * The test suite is available at the following URL.
 * https://tigerbytes2.lsu.edu/users/hchen11/lsl/LSL_benchmark.txt
 *
 * Comment: terminating, non-linear
 */

extern int __VERIFIER_nondet_int();

int main() {
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    while (4*x + y > 0) {
        int old_x = x;
        x = -2*old_x + 4*y;
        y = 4*old_x;
    }
    return 0;
}
