# Example 3: `Loopvar`

Boogie Model: [`loopvar.bpl`](loopvar.bpl) (1:1 translation) and [`loopvar_modified.bpl`](loopvar_modified.bpl) (with variant-tracking, see below)

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

`loopvar.bpl` is the 1:1 translation: the original `pragma Assert (X > 0)` becomes `assert x > 0;` at the end of the loop body, nothing else.

`loopvar_modified.bpl` simulates `pragma Loop_Variant (Increases => X)` using three elements:

*   **`x_old`:** Stores the variable's value from the previous iteration.
*   **`is_first`:** A flag to skip the comparison during the very first loop pass.
*   **`assert x > x_old;`:** Enforces that the value actually increased on all subsequent iterations.

## Results from Ultimate PA

### `loopvar.bpl`

| Type | Description |
|---|---|
| Assertion always holds | `assert x > 0;` |
| Loop Invariant (derived) | `0 < x` |
| Procedure Contract (derived) | `Modifies: []` |

**Overall Result: All specifications hold — 1 specification checked, all of them hold.**

### `loopvar_modified.bpl`

| Type | Description |
|---|---|
| Assertion always holds | `assert x > x_old;` |
| Assertion always holds | `assert x > 0;` |
| Loop Invariant (derived) | `(is_first && 1 <= x) \|\| (1 + x_old <= x && 2 <= x)` |
| Procedure Contract (derived) | `Modifies: []` |

**Overall Result: All specifications hold — 2 specifications checked, all of them hold.**
