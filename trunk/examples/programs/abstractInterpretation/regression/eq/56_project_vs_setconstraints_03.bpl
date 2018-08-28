//#Safe
/*
 */
procedure main() {
  var i, j : int;
  var a, b : [int] int;

  if (*) {
    a[i] := 1;
  } else {
    a[i] := 2;
  }

  a[j] := 3;
  
  assert a[i] == 1 || a[i] == 2 || a[i] == 3;
}
