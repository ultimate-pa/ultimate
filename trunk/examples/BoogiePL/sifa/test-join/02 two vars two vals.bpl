//#Safe
// set block encoding to single statement to test join
procedure f() returns ()
{
  var i, j : int;
  if (*) {
    i := 0;
  } else {
    j := 1;
  }
  assert true;
}
