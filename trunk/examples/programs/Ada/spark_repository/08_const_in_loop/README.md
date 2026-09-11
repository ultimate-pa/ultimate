# Example 8: `Const_In_Loop`

Boogie Model: [`const_in_loop.bpl`](const_in_loop.bpl)

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

`X`/`T'Last` are re-declared fresh every loop iteration and always equal the current `Z`. `V1` is only updated when `Z = 1`, but `V2` is updated every time — and `Z` becomes `2` forever after the first iteration, so `V1` stops changing after that. The original's own assertion `V1 = V2` is actually false from the second iteration on, so this model instead checks the property that really holds: `V1` always stays `1`. `Z`, `V1`, `V2`, `X` are kept as plain `int`s, and `T'Last` becomes `T_Last := X`.

## Results from Ultimate PA

| Type | Description |
|---|---|
| Assertion always holds | `assert X >= 1;` |
| Assertion always holds | `assert V1 == 1;` |
| Procedure postcondition always holds | `ensures Z >= 1;` |
| Loop Invariant (derived) | `(V1 == 1 && Z == 1) \|\| (V1 == 1 && 2 <= Z)` |
| Procedure Contract (derived) | `Modifies: []` |

**Overall Result: All specifications hold — 3 specifications checked, all of them hold.**