//#rNonTermination
/*
 * Date: 2014-06-06
 * Author: leike@informatik.uni-freiburg.de
 *
 * Example 2.17 from
 * https://tigerbytes2.lsu.edu/users/hchen11/lsl/LSL_benchmark.txt
 *
 * Comment: non-terminating (for x=0, y=11)
 */

int main(int x, int y) {
    while (x < 10) {
        x = -y;
        y++;
    }
    return 0;
}
