//#Safe
/*
 */
procedure main() {
  var i, j : int;
  var a : [int] int;

  assume i != j;

  if (*) {
    a[i] := 1;
  } else {
    a[i] := 2;
  }

  a[j] := 3;
  
  assert a[i] == 1 || a[i] == 2;
}
