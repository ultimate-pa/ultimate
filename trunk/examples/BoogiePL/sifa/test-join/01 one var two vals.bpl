//#Safe
// set block encoding to single statement to test join
procedure f() returns ()
{
  var i : int;
  if (*) {
    i := 0;
  } else {
    i := 1;
  }
  assert true;
}
