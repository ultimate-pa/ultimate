/* #Safe
*/

var x_glob, y_glob, z_glob: int;

procedure test_proc(x: int) returns (res: int);
requires x >=0;
ensures res > 0;
modifies z_glob;

implementation test_proc(x : int) returns (res: int)
{
  res := x + 1;
  z_glob := -1;
  return;
}


procedure Main() returns ();
modifies x_glob, y_glob, z_glob;

implementation Main() returns ()
{
  var z : int;
  x_glob:= 42;
  y_glob := x_glob;
  call z := test_proc(1);
  assert(z > 0);
}


