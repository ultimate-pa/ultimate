//#Safe
// set block encoding to single statement to test join
procedure f() returns ()
{
  var i, j : int;
  if (*) {
    i := 0;
    j := 2;
  } else {
	i := 1;
    j := 2;
  }
  assert true;
}
