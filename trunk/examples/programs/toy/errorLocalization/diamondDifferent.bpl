//#Unsafe
/*
 * Author: Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Date: 2017-06-02
 */


procedure main()
{
  var x, y: int;

  y := 1;
  havoc x;
  if (x > 0) {
    y := 0;
  } else {
    x := 0;
  }
  assert(y == 1);
}
