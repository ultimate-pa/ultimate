//#Unsafe
/*
 * Date: September 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

int nonMain() {
    int *p = malloc(sizeof(int));
    // @assert *p == 0;
    return 0;
}
