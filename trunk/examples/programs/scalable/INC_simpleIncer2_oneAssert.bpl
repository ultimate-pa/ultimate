//#Safe
// author: nutz@informatik.uni-freiburg.de

procedure SAS09paper()
{
  var x: int;
  var y: int;

  x := 0;
  y := 0;

  while (*) {
    if(*) {
	x := x + 1;
    }
    if(*) {
	y := y + 1;
    }
  }

  assert(x != -1 && y != -1);
}

