# Example 5: `Pi_Euler`

Boogie Model: [`pi_euler.bpl`](pi_euler.bpl)

Source: `../testsuite/gnatprove/tests/NC05-005__float_division/pi_euler.adb`

## Original Ada

    pragma SPARK_Mode;
    function Pi_Euler return Long_Float is
       Index: Positive;
       Pi, Erreur : Long_Float;
    begin
       Pi := 0.0;
       Index := 1;
       Erreur := 1.0;
       While not (Erreur<0.00000008) loop
          begin
             pragma Loop_Invariant (Index >= 1);
             pragma Assert (Long_Float(Index) >= 1.0);
             Erreur := 1.0/Long_Float(Index);  --  @FLOAT_OVERFLOW_CHECK:PASS
             Pi := Pi+Erreur;
             Index := Index+1;
          end;
       end loop;
       return (Pi);
    end Pi_Euler;

## Modeling Idea

`Index` stays an integer counter; `Pi` and `Erreur` become Boogie `real`s. The Ada conversion `Long_Float(Index)` is modeled with a function `ToReal`, so `1.0/Long_Float(Index)` becomes `Inv(index) = 1.0/ToReal(index)`. The loop condition `while not (Erreur < eps)` becomes `while (erreur >= eps)`. `assert index >= 1;` mirrors the original's `pragma Assert (Long_Float(Index) >= 1.0)`, which guarantees the division never happens at `Index = 0`.

## Results from Ultimate PA

| Type | Description |
|---|---|
| Assertion always holds | `assert ToReal(index) >= 1.0;` |
| Loop Invariant (derived) | `1 <= index` |
| Procedure Contract (derived) | `Modifies: []` |

**Overall Result: All specifications hold — 1 specifications checked, all of them hold.**