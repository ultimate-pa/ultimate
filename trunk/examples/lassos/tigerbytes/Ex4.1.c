//#rTermination
/*
 * Date: 2014-06-06
 * Author: leike@informatik.uni-freiburg.de
 *
 * Example 4.1 from
 * https://tigerbytes2.lsu.edu/users/hchen11/lsl/LSL_benchmark.txt
 *
 * Comment: terminating, non-linear
 */

int main(int x, int y, int z, int n) {
    while (x + y >= 0 && x <= n) {
        x = 2*x + y;
        y = z;
        z = z++;
    }
    return 0;
}
