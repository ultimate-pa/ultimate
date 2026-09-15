# Example 8: `Const_In_Loop`

Boogie Model: [`const_in_loop.bpl`](const_in_loop.bpl) (1:1 translation) and [`const_in_loop_modified.bpl`](const_in_loop_modified.bpl) (with the assert fixed, see below)

Source: `../testsuite/gnatprove/tests/M716-042__constants/const_in_loop.adb`

## Original Ada

```ada
procedure Const_In_Loop (Z : out Positive) is
   V1, V2 : Integer := 1;
begin
   Z := 1;
   while True loop
     declare
        X : constant Integer := Z;
        subtype T is Positive range 1 .. X;
     begin
        if Z = 1 then
           V1 := T'Last;
        end if;
        V2 := T'Last;
        pragma Assert (V1 = V2);
        pragma Loop_Invariant (V1 = T'Last);
        Z := 2;
     end;
   end loop;
end Const_In_Loop;
```

## Modeling Idea

`X`/`T'Last` are re-declared fresh every loop iteration and always equal the current `Z`. `V1` is only updated when `Z = 1`, but `V2` is updated every time — and `Z` becomes `2` forever after the first iteration, so `V1` stops changing after that. `Z`, `V1`, `V2`, `X` are kept as plain `int`s, and `T'Last` becomes `T_Last := X`.

`const_in_loop.bpl` is the 1:1 translation, keeping the original's own `pragma Assert (V1 = V2)` as `assert V1 == V2;`. `const_in_loop_modified.bpl` changes only that one line to `assert V1 == 1;`, the property that actually holds.

## Results from Ultimate PA

### `const_in_loop.bpl`

Ultimate proves this **incorrect** — `assert V1 == V2;` is violated, with a concrete counterexample:

    Z := 1; V1 := 1; V2 := 1;
    X := Z;  T_Last := X;
    COND TRUE  Z == 1;  V1 := T_Last;
    V2 := T_Last;
    Z := 2;
    X := Z;  T_Last := X;
    COND FALSE !(Z == 1);
    V2 := T_Last;
    assert V1 == V2;   -- V1 == 1, V2 == 2, fails

`V1` was only written on the first pass (`Z == 1`) and never touched again, while `V2` tracks the fresh `T_Last` every time — so after the second iteration `V1 == 1` but `V2 == 2`.

**Comparison with GNATprove** (`--level=4 --prover=all --proof=progressive:all`)

    const_in_loop.adb:14:24: medium: assertion might fail
       14 |            pragma Assert (V1 = V2);
          |                           ^~~~~~~
          + e.g. when V1 = 0
          and V2 = 2
          + possible fix: loop invariant at line 15 should mention V2
       15 |            pragma Loop_Invariant (V1 = T'Last);
          |            ^
          + provers reached time limit before completing the proof

- That suggested fix doesn't actually work: adding `V2 = T'Last` to the loop invariant still gives `medium: assertion might fail`, same counterexample, even at max effort.
- The counterexample `V1 = 0, V2 = 2` isn't even a real reachable program state (`V1` is always `1` in any actual execution, never `0`).
- GNATprove needs the invariant handed to it and has no counterexample-guided refinement loop. Ultimate PA, by contrast, either derives a sufficient invariant on its own or, as here, returns a concrete, checkable counterexample trace over an actual reachable execution.

### `const_in_loop_modified.bpl`

| Type | Description |
|---|---|
| Assertion always holds | `assert X >= 1;` |
| Assertion always holds | `assert V1 == 1;` |
| Procedure postcondition always holds | `ensures Z >= 1;` |
| Loop Invariant (derived) | `(V1 == 1 && Z == 1) \|\| (V1 == 1 && 2 <= Z)` |
| Procedure Contract (derived) | `Modifies: []` |

**Overall Result: All specifications hold — 3 specifications checked, all of them hold.**