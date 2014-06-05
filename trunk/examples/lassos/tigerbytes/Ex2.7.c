//#rTermination
/*
 * Date: 2014-06-06
 * Author: leike@informatik.uni-freiburg.de
 *
 * Example 2.7 from
 * https://tigerbytes2.lsu.edu/users/hchen11/lsl/LSL_benchmark.txt
 *
 * Comment: terminating, non-linear
 */

int main(int x, int y) {
    while (x > 0 && x < y) {
        x = 2*x;
        y++;
    }
    return 0;
}
