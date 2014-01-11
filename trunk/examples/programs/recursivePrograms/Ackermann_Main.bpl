//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2.8.2010
 * 
 * The Ackermann function.
 * Implementation the version defined by Rózsa Péter.
 * http://en.wikipedia.org/wiki/Ackermann_function
 * The program is correct with respect to the ensures statement.
 */

procedure ackermann(m,n: int) returns (res: int);
free requires m >=0;
free requires n >=0;
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


procedure Main(x,y: int) returns (z: int);
ensures (x>0 && y>0) ==> z>0;

implementation Main(x,y: int) returns (z: int)
{
  call z := ackermann(x,y);
}
