//#Safe
procedure main() {
  var i, j, k, x, y : int;
  var a, b : [int] int;

  assume b[j] == 0;
  a[j] := 7;

  
  k := j;

  havoc j;

  while (*) {
    assume b[i] == 1;
    a[i] := 13;
    havoc i;
  }
  
  assert a[k] == 7;
}
