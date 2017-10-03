//NonTerminating
/*
 * Shows bug in BlockEncoding.
 * Modification of Urban-WST2013-Fig2-modified1000.bpl
 *
 * Date: 2017-10-03
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

var x1,x2: int;

procedure main()
modifies x1,x2;
{
    while (x1 <= 10) {
//         x2 := 1000;
        while (*) {
//             x2 := x2 - 1;
        }
        x1 := x1 - 1;
    }

}
