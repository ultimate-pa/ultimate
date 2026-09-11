# Example 7: `My_Find`

Boogie Model: [`my_find.bpl`](my_find.bpl)

Source: `../testsuite/gnatprove/tests/PC14-014__functional/use_ordered_sets.adb`

## Original Ada

    function My_Find (S : My_Sets.Set; E : Element_Type) return Cursor is
       Cu : Cursor := First (S);
    begin
       while Has_Element (S, Cu) loop
          pragma Loop_Invariant
            (for all I in 1 .. P.Get (Positions (S), Cu) - 1 =>
               Formal_Model.E.Get (Elements (S), I) /= E);
          if Element (S, Cu) = E then
             return Cu;
          end if;
          Cu := Next (S, Cu);
       end loop;
       return No_Element;
    end My_Find;

## Modeling Idea

SPARK's formal model maps cursors to positions and positions to elements; this is simplified to a plain Boogie array `Elems`, with an integer loop index `i` standing in for the cursor. The distinction between `Cursor` and `Position` is dropped — the position is used directly as the loop variable. If no match is found, the closing `assert` checks that `e` doesn't occur anywhere in the array.

## Results from Ultimate PA

| Type | Description |
|---|---|
| Assertion always holds | The concluding `assert` confirming `e` is not in the array. |
| Loop Invariant (derived) | `(forall v_skolemized_qk_6 : int :: (v_skolemized_qk_6 < 1 \|\| Elems[v_skolemized_qk_6] != e) \|\| i < v_skolemized_qk_6 + 1)` |
| Procedure Contract (derived) | `Modifies: []` |

**Overall Result: All specifications hold — 1 specifications checked, all of them hold.**