//#iSafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 10.5.2011
 *
 * Recursive and imperative implementation of McCartys 91 function.
 */

procedure McCarthyRec(x: int) returns (res: int);

implementation McCarthyRec(x: int) returns (res: int)
{
  if (x>100) {
    res := x-10;
  }
  else {
    call res :=  McCarthyRec(x + 11);
    call res := McCarthyRec(res);
  }
}


procedure McCarthyImp(x: int) returns (res: int);

implementation McCarthyImp(x: int) returns (res: int)
{
  if (x <= 101) {
    res := 91;
  }
  else {
    res := x - 10;
  }
}




procedure Main(a: int);

implementation Main(a: int)
{
  var b, c: int;
  call b := McCarthyRec(a);
  call c := McCarthyImp(a);
  assert(b == c);
}
