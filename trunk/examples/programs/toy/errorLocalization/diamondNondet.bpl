//#Unsafe
/*
 * Author: Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Date: 2017-06-02
 */


procedure main()
{
  var x, y: int;

  y := 0;
  if (*) {
    x := 0;
  } 
  assert(x != 0 || y != 0);
}
