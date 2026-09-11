var Elems: [int]int;

procedure MyFind(n: int, e: int) returns (found: bool, pos: int)
  requires n >= 0;
{
  var i: int;

  i := 1;
  found := false;
  pos := 0;

  while (i <= n)
  {
    if (Elems[i] == e) {
      found := true;
      pos := i;
      return;
    }
    i := i + 1;
  }

  assert (forall k: int :: 1 <= k && k <= n ==> Elems[k] != e);
}
