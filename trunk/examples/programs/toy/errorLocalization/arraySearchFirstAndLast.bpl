//#Unsafe
/*
 * Search the first and the last occurrences of x in an array.
 * The program has a bug: f should be initialized with '-1'.
 *
 * Author: Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Date: 2017-07-04
 */

procedure main() returns () {
    var i,f,l,n,x: int;
    var a: [int]int;
    
    assume n >= 0;
    f := 0; // first occurrence of x in a
    l := -1; // last occurrence of x in a
    i := 0;
    while (i < n) {
        if (f == -1) {
            if (a[i] == x) {
                f := i;
                l := i;
            }
        } else {
            if (a[i] == x) {
                l := i;
            }
        }
        i := i + 1;
        assert f <= l && l < n;
    }
}
