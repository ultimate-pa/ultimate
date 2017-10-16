//#Safe
/*
 * Checks that we can derive something like a framing condition.
 * test is reduced to a minimum, real use case would involve a procedure call
 * that introduced the old version of the array.
 * b would be something like the valid array
 */
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
