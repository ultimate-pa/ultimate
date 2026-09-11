var OldS1: [int]int;
var S2: [int]int;

procedure Move2(n0: int)
  modifies S2;
  requires n0 >= 0;
{
  var k: int;

  k := 0;

  while (k < n0)
    // corresponds to: for all I in 1..Length(S2) => Elements(S2)[I] = Elements(S1)'Loop_Entry[I]
    // "Length(S1) = Length(S1)'Loop_Entry - Length(S2)" is implicit here:
    // the remaining length is n0 - k and does not need to be tracked separately.
  {
    // Cu = First(S1) always corresponds to position k+1 in the original array
    S2[k + 1] := OldS1[k + 1]; // Include (S2, Element (S1, Cu))
    k := k + 1;
    // Exclude (S1, ...) and Cu := First (S1) are implicit: the "remaining
    // S1" is, by construction, OldS1[k+1 .. n0]; a physical shift
    // is not modeled (see README, Simplifications section).
  }

  assert (forall i: int :: 1 <= i && i <= n0 ==> S2[i] == OldS1[i]);
}
