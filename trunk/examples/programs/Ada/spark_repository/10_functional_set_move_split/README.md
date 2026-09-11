# Example 10: `Move_2`

Boogie Model: [`move_2.bpl`](move_2.bpl)

Source: `../testsuite/gnatprove/tests/PC14-014__functional/use_ordered_sets.adb`

## Original Ada

    procedure Move_2 (S1, S2 : in out My_Sets.Set) is
       Cu : Cursor := First (S1);
    begin
       Clear (S2);
       while Has_Element (S1, Cu) loop
          pragma Loop_Invariant (P.Get (Positions (S1), Cu) = 1);
          pragma Loop_Invariant
            (Length (S1) = Length (S1)'Loop_Entry - Length (S2));
          pragma Loop_Invariant
            (for all I in 1 .. Length (S2) =>
                 E.Get (Elements (S2), I) = E.Get (Elements (S1)'Loop_Entry, I));
          pragma Loop_Invariant
            (for all I in 1 .. Length (S1) =>
                 E.Get (Elements (S1), I) =
                 E.Get (Elements (S1)'Loop_Entry, Length (S2) + I));
          Include (S2, Element (S1, Cu));
          Exclude (S1, Element (S1, Cu));
          Cu := First (S1);
       end loop;
    end Move_2;

## Modeling Idea

`Move_2` removes the smallest element of `S1` each iteration and appends it to `S2`; after `n0` iterations, `S2` is a copy of the original `S1`. `S1`'s starting state is frozen once as `OldS1`. Since both are ordered sets, elements always come out in the same order they started in, so the "remaining" `S1` after `k` steps is just `OldS1[k+1..n0]` — no need to actually shift a second array. The first two invariants of the original hold automatically here, since `k` is the only loop variable. The interesting third invariant is that `S2` matches the matching prefix of `OldS1`.

## Results from Ultimate PA

| Type | Description |
|---|---|
| Assertion always holds | `assert (forall i: int :: 1 <= i && i <= n0 ==> S2[i] == OldS1[i]);` |
| Loop Invariant (derived) | `(forall v6: int :: (v6 < 1 \|\| k < v6) \|\| S2[v6] == OldS1[v6])` |
| Procedure Contract (derived) | `Modifies: [S2]` |

**Overall Result: All specifications hold — 1 specification checked, all of them hold.**