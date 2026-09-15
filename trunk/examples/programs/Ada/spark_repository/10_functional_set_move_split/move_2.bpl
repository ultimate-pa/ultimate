var OldS1: [int]int;
var S2: [int]int;

procedure Move2(n0: int)
  modifies S2;
  requires n0 >= 0;
{
  var k: int;

  k := 0;

  while (k < n0)
  {
    S2[k + 1] := OldS1[k + 1];
    k := k + 1;
  }

  assert (forall i: int :: 1 <= i && i <= n0 ==> S2[i] == OldS1[i]);
}
