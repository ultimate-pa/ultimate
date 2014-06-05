//#rTermination
/*
 * Date: 2014-06-06
 * Author: leike@informatik.uni-freiburg.de
 *
 * Example 3.3 from
 * https://tigerbytes2.lsu.edu/users/hchen11/lsl/LSL_benchmark.txt
 *
 * Comment: terminating, non-linear
 */

int main(int x, int y, int z) {
    while (x > 0) {
        x = x + y;
        y = y + z;
        z--;
    }
    return 0;
}
