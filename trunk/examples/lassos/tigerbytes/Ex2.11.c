//#rNonTermination
/*
 * Date: 2014-06-06
 * Author: leike@informatik.uni-freiburg.de
 *
 * Example 2.11 from
 * https://tigerbytes2.lsu.edu/users/hchen11/lsl/LSL_benchmark.txt
 *
 * Comment: non-terminating (for x=9,y=7)
 */

int main(int x, int y) {
    while (4*x - 5*y > 0) {
        int old_x = x;
        x = 2*old_x + 4*y;
        y = 4*old_x;
    }
    return 0;
}
