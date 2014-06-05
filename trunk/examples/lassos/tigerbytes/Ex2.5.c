//#rNonTermination
/*
 * Date: 2014-06-06
 * Author: leike@informatik.uni-freiburg.de
 *
 * Example 2.5 from
 * https://tigerbytes2.lsu.edu/users/hchen11/lsl/LSL_benchmark.txt
 *
 * Comment: non-terminating (for x=-1,y=0)
 */

int main(int x, int y) {
    while (x < y) {
        x = x + y;
        y = y / 2;
    }
    return 0;
}
