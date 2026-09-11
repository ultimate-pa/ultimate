# Example 3: `Loopvar`

Boogie Model: `loopvar.bpl`

Source: `../testsuite/gnatprove/tests/QC08-010__loopvar/loopvar.adb`

## Original Ada
```ada
procedure Loopvar with SPARK_Mode is 
   X : Integer := 1; 
begin
   while X < 10 loop
      pragma Loop_Variant (Increases => X);
      X := X + 1;
      pragma Assert (X > 0);
   end loop;
end Loopvar;
```

## Modeling Idea

Boogie has no direct equivalent of SPARK's `pragma Loop_Variant (Increases => X)`. Instead, `x_old` stores the value from the previous iteration, and a flag `is_first` skips the check on the very first pass. From the second iteration on, `assert x > x_old;` checks that `x` really increased. The original `pragma Assert (X > 0)` becomes `assert x > 0;` at the end of the loop body.

## Results from Ultimate PA

| Type | Description |
|---|---|
| Assertion always holds | `assert x > x_old;` |
| Assertion always holds | `assert x > 0;` |
| Loop Invariant (derived) | `(is_first && 1 <= x) || (1 + x_old <= x && 2 <= x)` |
| Procedure Contract (derived) | `Modifies: []` |

**Overall Result: All specifications hold — 2 specifications checked. All of them hold.**
