//#Safe
procedure main() {
  var a, b, a_old : [int] int;
  var i, j, k : int;

  a_old := a;
  while (*) {
    assume b[i] == 1;
    a[i] := 42;
    havoc i;
  }
  //assert a[j] == a_old[j] || b[j] == 1;
  assume b[j] != 1;
  assert a[j] == a_old[j];
}
