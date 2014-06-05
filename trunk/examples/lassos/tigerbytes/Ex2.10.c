//#rTermination
/*
 * Date: 2014-06-06
 * Author: leike@informatik.uni-freiburg.de
 *
 * Example 2.10 from
 * https://tigerbytes2.lsu.edu/users/hchen11/lsl/LSL_benchmark.txt
 *
 * Comment: terminating, linear
 */

int main(int x, int y) {
    while (x > 0 && y < 0) {
        x = x + y;
        y--;
    }
    return 0;
}
