//#rTermination
/*
 * Date: 2014-06-06
 * Author: leike@informatik.uni-freiburg.de
 *
 * Example 2.9 from
 * https://tigerbytes2.lsu.edu/users/hchen11/lsl/LSL_benchmark.txt
 *
 * Comment: terminating, non-linear
 */

int main(int x, int y, int n) {
    while (x > 0 && x < n) {
        x = -x + y - 5;
        y = 2*y;
    }
    return 0;
}
