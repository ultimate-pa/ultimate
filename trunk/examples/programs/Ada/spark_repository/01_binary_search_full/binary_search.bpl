// binary_search.bpl
// Model of ug__binary_search_final/binary_search.adb
var A: [int]int;

procedure Search(lo: int, hi: int, key: int) returns (found: bool, pos: int)
  requires lo <= hi;
  requires (forall i, j: int :: lo <= i && i <= j && j <= hi ==> A[i] <= A[j]);
  ensures found ==> (lo <= pos && pos <= hi && A[pos] == key);
  ensures !found ==> (forall i: int :: lo <= i && i <= hi ==> A[i] != key);
{
  var left, right, med: int;

  left := lo;
  right := hi;
  found := false;
  pos := 0;

  while (left <= right)
  {
    med := left + (right - left) / 2;
    assert lo <= med && med <= hi;

    if (A[med] < key) {
      assert (forall i1: int :: lo <= i1 && i1 <= med ==> A[i1] <= A[med]);
      left := med + 1;
    } else if (A[med] > key) {
      assert (forall i2: int :: med <= i2 && i2 <= hi ==> A[med] <= A[i2]);
      right := med - 1;
    } else {
      found := true;
      pos := med;
      return;
    }
  }
  assert (forall i: int :: lo <= i && i <= hi ==> A[i] != key);
}
