//#Safe
// author: nutz@informatik.uni-freiburg.de
procedure SAS09paper()
{
  var x: int;
  var y: int;
  var z: int;
  var a: int;

  x := 0;
  y := 0;
  z := 0;
  a := 0;

  while (*) {
    if(*) {
	x := x + 1;
    }
    if(*) {
	y := y + 1;
    }
    if(*) {
	z := z + 1;
    }
    if(*) {
	a := a + 1;
    }
  }

  assert(x != -1 && y != -1 && z != -1 && a != -1 );
}

