//#rNonTermination
/*
 * Date: 2014-06-06
 * Author: leike@informatik.uni-freiburg.de
 *
 * Example 2.12 from
 * https://tigerbytes2.lsu.edu/users/hchen11/lsl/LSL_benchmark.txt
 *
 * Comment: non-terminating (for x=0,y=0)
 */

int main(int x, int y) {
    while (x < 5) {
        int old_x = x;
        x = old_x - y;
        y = old_x + y;
    }
    return 0;
}
