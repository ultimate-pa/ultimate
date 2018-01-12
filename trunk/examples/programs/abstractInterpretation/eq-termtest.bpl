/*
 * if the map equality domain works precisely, (and has no special measures to 
 * ensure termination,) this example should not terminate.
 * (still may have to double check..)
 */
procedure main() {
  var a : [int] int;
  var v : [int] int;
  var i, j : int;

  //a[0] := 0;
  //a[i] := 0;
  assume a[0] == 0 && a[i] == 0 && v[i] == 1 && v[0] == 1;

  while (*) {
    assume v[j] == 0;
    v[j] := 1;
    a[j] := i;
    i := j;
    havoc j;
    // a[0] = 0 && a^n[i] = 0 && v[a^k[i]] == 1 forall k <= n
  }

  assert v[a[a[i]]] == 1;
}
