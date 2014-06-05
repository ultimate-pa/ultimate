//#rNonTermination
/*
 * Date: 2014-06-06
 * Author: leike@informatik.uni-freiburg.de
 *
 * Example 3.2 from
 * https://tigerbytes2.lsu.edu/users/hchen11/lsl/LSL_benchmark.txt
 *
 * Comment: non-terminating (for x>0, y>=0, z>=0)
 */

int main(int x, int y, int z) {
    while (x > 0) {
        x = x + y;
        y = y + z;
    }
    return 0;
}
