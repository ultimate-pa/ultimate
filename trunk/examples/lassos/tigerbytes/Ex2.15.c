//#rNonTermination
/*
 * Date: 2014-06-06
 * Author: leike@informatik.uni-freiburg.de
 *
 * Example 2.15 from
 * https://tigerbytes2.lsu.edu/users/hchen11/lsl/LSL_benchmark.txt
 *
 * Comment: non-terminating (for x>0,y>=0)
 */

int main(int x, int y) {
    while (x > 0) {
        x = x + y;
    }
    return 0;
}
