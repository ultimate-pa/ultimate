//#rNonTermination
/*
 * Date: 2014-06-06
 * Author: leike@informatik.uni-freiburg.de
 *
 * Example 2.14 from
 * https://tigerbytes2.lsu.edu/users/hchen11/lsl/LSL_benchmark.txt
 *
 * Comment: non-terminating (for x=10k, y=3k, any k>0)
 */

int main(int x, int y) {
    while (x > 0 && y > 0) {
        x = 10*y - 2*x;
    }
    return 0;
}
