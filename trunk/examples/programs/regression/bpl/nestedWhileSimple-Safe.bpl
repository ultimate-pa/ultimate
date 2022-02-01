//#Safe
//author: nutz@informatik.uni-freiburg.de
procedure main()
{
  var x: int;

  x := 0;

  while (*) {
    x := x + 1;
    while (*) {
      x := x + 1;
      while (*) {
        x := x + 1;
        while (*) {
          x := x + 1;
          while (*) {
            x := x + 1;
          }
        }
      }
    }
  }

  assert(x != -1);
}

