//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2.8.2010
 * 
 * The ackermann function.
 * Implementation the version defined by Rózsa Péter.
 * http://en.wikipedia.org/wiki/ackermann_function
 * The program is correct with respect to the ensures statement.
 */

procedure ackermann(m,n: int) returns (res: int);
requires m >=0;
requires n >=0;
ensures res >=0;

implementation ackermann(m,n : int) returns (res: int)
{
  var tmp: int;

  if (m==0) {
    res := n+1;
    return;
  }
  if (n==0) {
    call res := ackermann(m-1,1);
    return;
  }
  call tmp := ackermann(m,n-1);
  call res := ackermann(m-1,tmp);
}


