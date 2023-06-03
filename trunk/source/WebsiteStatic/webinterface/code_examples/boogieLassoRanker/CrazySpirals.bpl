//#rTermination
/*
 * Date: 2014-06-08
 * Author: leike@informatik.uni-freiburg.de
 *
 * This program consists of two spirals.
 * The vector (c, d) spirals around (0, 0) and the
 * the vector (a, b) does a skewed spiral around (0, 0),
 * but this spiral is modified by c.
 *
 * This program terminates, because on average, (c, d) and (a, b) are (0, 0).
 *
 * It has the following 7-nested ranking function.
 * f0 = 8000*q - 250*a - 625*b + 25*c + 50*d
 * f1 = 6000*q + 250*a - 625*b - 55*c - 10*d
 * f2 = 125*a - 16*c - 37*d
 * f3 = 2356*q - 58*a - 145*b + 29*c - 16*d
 * f4 = 140*q + 21*a - 20*b + 4*c
 * f5 = 13*q + 4*a
 * f6 = q
 */

procedure main() returns ()
{
  var q, a, b, c, d: real;
  while (q > 0.0) {
    q    := q + a - 1.0;
    a, b := 3.0*a - 5.0*b + c, 12.0*a + 3.0*b;
    c, d := 3.0*c - 4.0*d, 4.0*c + 3.0*d;
  }
}
