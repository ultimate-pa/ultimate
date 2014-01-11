//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 25.5.2010
 *
 * Reveales bug in revision r3739.
 * requires m >=0; is translated to assert(m>=0) in foo
 * requires old(g) == g; is translated to assert(old(g) == g) in foo
 * 
 * Fixed in revision r3743, now
 * requires m >=0; is translated to assert(n>=0) in foo
 * requires old(g) == g; is translated to assert(g == g) in foo
 */

var g: int;

procedure foo(n: int) returns (res: int);
modifies g;

implementation foo(n: int) returns (res: int)
{
  assume (n == 0);
  g := g+1;
  call res := bar(n);
}
  


procedure bar(m: int) returns (res: int);
requires m >=0;
requires old(g) == g;


implementation bar(m: int) returns (res: int)
{
  res := 0;
}