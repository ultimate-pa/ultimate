/*
 * Program from Fig.9a of a technical report which is based on
 * 2013CAV - Brockschmidt,Cook,Fuhs - Better termination proving through cooperation
 *
 * Date: 2014
 * Author: Matthias Heizmann
 *
 */
var k, i, j, n: int;

procedure main()
modifies k, i, j, n;
{
  if ( k >= 1) {
    i := 0;
    while (i < n) {
      j := 0;
      while (j <= i) {
        j := j + k;
      }
      i := i + 1;
    }
  }
}
