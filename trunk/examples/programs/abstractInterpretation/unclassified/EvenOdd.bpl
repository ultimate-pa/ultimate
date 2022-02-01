//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 8.5.2011
 *
 * Mutual recursive procedure calls.
 */


procedure main(z: int);

implementation main(z: int)
{
  var y: bool, x:int;
  if ( z == 6 ) {
     call y := even(z);
  }
  else {
    if (z == 5) {
      call y := even(z+1);
    }
    else {
       call y := even(6);
    }
  }
  assert y == true;
}


procedure even(n: int) returns (res: bool);

implementation even(n: int) returns (res: bool)
{
  if (n == 0) {
    res := true;
    return;
  }
  else {
    call res := odd(n-1);
  }
}
  
  
procedure odd(n: int) returns (res: bool);

implementation odd(n: int) returns (res: bool)
{
  if (n == 0) {
    res := false;
    return;
  }
  else {
    call res := even(n-1);
  }
}