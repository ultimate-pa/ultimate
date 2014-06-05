//#rNonTermination
/*
 * Date: 2014-06-06
 * Author: leike@informatik.uni-freiburg.de
 *
 * Example 3.6 from
 * https://tigerbytes2.lsu.edu/users/hchen11/lsl/LSL_benchmark.txt
 *
 * Comment: non-terminating (for x=-1, y=1, z=-1)
 */

int main(int x, int y, int z) {
    while (x < 0) {
        x = x + z;
        z = -2*y;
        y = y + 1;
    }
    return 0;
}
