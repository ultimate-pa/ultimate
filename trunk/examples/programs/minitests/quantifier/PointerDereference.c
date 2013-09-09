//#iSafe
/*
 * Date: September 2013
 * Author: heizmann@informtik.uni-freiburg.de
 * 
 */

int main() {
    int *p = malloc(sizeof(int));
    *p = 3;
    free(p);
    return 0;
}
