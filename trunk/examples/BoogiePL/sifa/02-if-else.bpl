procedure f() returns ()
{
  var i : int;
  if (*) {
    i := 0;
  } else {
    i := 1;
  }
  assert i == 0 || i == 1;
  assert i == 0;
}
