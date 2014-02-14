//#Safe
/*
 * Date: September 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

int main() {
    int *p = malloc(sizeof(int));
    int *q = malloc(sizeof(int));
    // @assert  p != q;
    free(p);
    free(q);
}
