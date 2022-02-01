//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2014-07-06
 * I stumbled upon this program while analyzing why we cannot show memory 
 * safety in the termination competition 2014.
 * 
 * Similar programs like this occur in real-life:
 * Consider the array a as a string (array of chars).
 * Consider the 23 as the null character '\0' which is the last character of
 * a string.
 * Diffrence to real world string is that here, we access not each position
 * of array.
 * 
 */

procedure main() returns ()
{
    var a : [int]int;
    var n : int;
    var i : int;

    assume n >= 0;
    a[n * 4] := 23;
    i := 0;
    while (a[i] != 23)
    // invariant i % 4 == 0 && a[n*4] == 23;
    {
      i := i + 4;
      assert i <= n * 4;
    }
}
