# Example 9: `Add_1` 

Boogie Model: [`add_1.bpl`](add_1.bpl)

Source: `../testsuite/gnatprove/tests/R516-050__functional_lists/use_lists.adb`
(identical also in `O722-006__functional_lists/use_lists.adb`)

## Original Ada

    package body Use_Lists with SPARK_Mode is
       procedure Add_1 (L1 : List; L2 : out List) is
          Cu : Cursor := First (L1);
       begin
          Clear (L2);
          while Has_Element (L1, Cu) loop
            pragma Loop_Invariant
               (Cursor_Sequence.Find (Get_Cursor_Model (L1), Cu) = Length (L2));
             pragma Loop_Invariant
               (for all N in 0 .. Natural (Length (L2)) - 1 =>
                     Is_Incr (Get (Get_Element_Model (L1), N),
                              Get (Get_Element_Model (L2), N)));
             if Element (L1, Cu) < Integer'Last then
                Append (L2, Element (L1, Cu) + 1);
             else
                Append (L2, Element (L1, Cu));
                pragma Assert
                  (Get (Get_Element_Model (L2), Length (L2) - 1) =
                     Element (L1, Cu));
             end if;
             pragma Assert (Is_Incr (Element (L1, Cu),
                            Get (Get_Element_Model (L2), Length (L2) - 1)));
             Next (L1, Cu);
          end loop;
       end Add_1;
    end Use_Lists;

## Modeling Idea

`L1`/`L2` are modeled as Boogie arrays with a loop index `i` running from `0` to `n-1`, mirroring SPARK's 0-indexed formal list model. `IsIncr` isn't a function in the original; it's added here to express the saturating increment: normally `y = x + 1`, but capped at `Integer'Last` (`2147483647`) instead of overflowing. The original's first Loop_Invariant is automatic here, since `i` already tracks `L2`'s length. The interesting second invariant is that every already-written position of `L2` is `IsIncr` of `L1`. `L1` also needed an added precondition bounding its values to `Integer'Last`, since without it Boogie's unbounded integers would let the saturating case fail to hold.

## Results from Ultimate PA

| Type | Description |
|---|---|
| Assertion always holds | `assert IsIncr(L1[i], L2[i]);` |
| Assertion always holds | `assert (forall k: int :: 0 <= k && k < n ==> IsIncr(L1[k], L2[k]));` |
| Loop Invariant (derived) | `((0 == i && 0 <= n) && (forall qk: int :: (L1[qk] < 2147483648 \|\| n < qk + 1) \|\| qk < 0)) \|\| ((((forall v6: int :: ((L1[v6] < 2147483647 \|\| v6 < 0) \|\| i < v6 + 1) \|\| 2147483647 == L2[v6]) && 0 <= n) && (forall v6: int :: ((L1[v6] == 2147483647 \|\| L2[v6] == L1[v6] + 1) \|\| v6 < 0) \|\| i < v6 + 1)) && (forall qk: int :: (L1[qk] < 2147483648 \|\| n < qk + 1) \|\| qk < 0)) && 1 <= i)` |
| Procedure Contract (derived) | `Modifies: [L2]` |

**Overall Result: All specifications hold — 2 specifications checked, all of them hold.**