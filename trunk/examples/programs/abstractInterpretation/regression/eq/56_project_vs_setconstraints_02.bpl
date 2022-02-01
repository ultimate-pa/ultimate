//#Safe
/*
 */
procedure main() {
  var i : int;
  var a, b : [int] int;

  if (*) {
    a[i] := 1;
  } else {
    a[i] := 2;
  }

  b := a;
  // this havoc triggers the imprecision (as of 27.08.2018)
  havoc a;
  
  assert b[i] == 1 || b[i] == 2;
}
