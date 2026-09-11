# Example 1: `Binary_Search.Search`

Boogie Model: [`binary_search.bpl`](binary_search.bpl)

Source: `../testsuite/gnatprove/tests/ug__binary_search_final/binary_search.adb`

## Original Ada

    function Search (A : Ar; I : Integer) return Opt_Index is
       Left  : Index;
       Right : Index;
       Med   : Index;
    begin
       if Empty (A) then
          return No_Index;
       end if;

       Left  := A'First;
       Right := A'Last;

       if Left = Right and A (Left) = I then
          return Left;
       elsif A (Left) > I or A (Right) < I then
          return No_Index;
       end if;

       while Left <= Right loop
          pragma Loop_Variant (Increases => Left, Decreases => Right);
          pragma Loop_Invariant (Left in A'Range and Right in A'Range);
          pragma Loop_Invariant
            (for all Index in A'First .. Left - 1 => A (Index) < I);
          pragma Loop_Invariant
            (for all Index in A'Range =>
               (if Index > Right then I < A (Index)));

          Med := Left + (Right - Left) / 2;

          if A (Med) < I then
             Left := Med + 1;
          elsif A (Med) > I then
             Right := Med - 1;
          else
             return Med;
          end if;
       end loop;

       return No_Index;
    end Search;

## Modeling Idea

- `A'First`/`A'Last` become the parameters `lo`/`hi`; the array itself becomes a global Boogie map `A: [int]int`.
- Since the array must be sorted for binary search to make sense, that's added as a precondition.
- The bounds check on `Med` and the two branch assertions from the Ada code are kept as `assert`s, so Ultimate has the same intermediate steps GNATprove does.
- The `Empty(A)`/`Left = Right` special cases before the loop are left out; they don't affect the loop invariant.
- An overflow check for `Med := Left + (Right - Left) / 2` was tried but broke Ultimate's proof search internally, so it's left out (Boogie's integers are unbounded anyway).

## Results from Ultimate PA

| Type | Description |
|---|---|
| Assertion always holds | `assert lo <= med && med <= hi;` |
| Assertion always holds | `assert (forall i1: int :: lo <= i1 && i1 <= med ==> A[i1] <= A[med]);` |
| Assertion always holds | `assert (forall i2: int :: med <= i2 && i2 <= hi ==> A[med] <= A[i2]);` |
| Assertion always holds | `assert (forall i: int :: lo <= i && i <= hi ==> A[i] != key);` (final assert after the loop) |
| Procedure postcondition always holds | `ensures found ==> (lo <= pos && pos <= hi && A[pos] == key);` |
| Procedure postcondition always holds | `ensures !found ==> (forall i: int :: lo <= i && i <= hi ==> A[i] != key);` |
| Procedure Contract (derived) | `Modifies: []` |

**Overall Result: All specifications hold — 6 specifications checked, all of them hold.**