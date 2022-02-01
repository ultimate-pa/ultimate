//#rTerminationDerivable
/*
 * Date: 08.10.2013
 * Author: leike@informatik.uni-freiburg.de
 *
 * An example tailored to the piecewise ranking template
 */

procedure main() returns (p: int, q: int, y: int, z: int) {
    assume(true);
    while (q > 0 && p > 0) {
        if (q < p) {
            q := q - 1;
            havoc p;
        } else if (p < q) {
            p := p - 1;
            havoc q;
        } else {
            assume(false);
        }
    }
}

