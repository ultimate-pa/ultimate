var L1: [int]int;
var L2: [int]int;

function IsIncr(x: int, y: int) returns (bool)
{
  (x < 2147483647 && y == x + 1) || (x == 2147483647 && y == x)
}

procedure Add1(n: int)
  modifies L2;
  requires n >= 0;
  requires (forall k: int :: 0 <= k && k < n ==> L1[k] <= 2147483647);
{
  var i: int;

  i := 0;

  while (i < n)
  {
    if (L1[i] < 2147483647) {
      L2[i] := L1[i] + 1;
    } else {
      L2[i] := L1[i];
    }
    assert IsIncr(L1[i], L2[i]);
    i := i + 1;
  }

  assert (forall k: int :: 0 <= k && k < n ==> IsIncr(L1[k], L2[k]));
}
