# Example 6: `Pi_Euler_2`

Boogie Model: [`pi_euler_2.bpl`](pi_euler_2.bpl)

Source: `../testsuite/gnatprove/tests/NC05-005__float_division/pi_euler_2.adb`

## Original Ada

    pragma SPARK_Mode;
    function Pi_Euler_2 return Long_Float is
       Index: Long_Integer range 1 .. Long_Integer'Last;
       Pi, Erreur : Long_Float;
       Index_Float : Long_Float range 1.0 .. Long_Float'Last;
    begin
       Pi := 0.0;
       Index := 1;
       Index_Float := 1.0;
       Erreur := 1.0;
       While not (Erreur<0.00000008) loop
          begin
             -- erreur := 1.0/Long_Float(Index)/Long_Float(Index);
             -- bug GNATprove sur les conversion Entier <=> Flottants
             pragma Loop_Invariant (Index_Float >= 1.0);
             Pragma Assert (Index_Float >= 1.0);
             Erreur := 1.0/Index_Float/Index_Float;
             Pi := Pi+Erreur;
             Index := Index+1;
             Index_Float := Index_Float + 1.0;
          end;
       end loop;
       return (Pi);
    end Pi_Euler_2;

## Modeling Idea

Unlike Example 5, the float counter is tracked directly: `indexFloat` is a separate `real` variable, updated in parallel with the integer `index`, rather than converted on the fly. `indexFloat >= 1.0` guarantees the division by `indexFloat * indexFloat` never hits zero.

## Results from Ultimate PA

| Type | Description |
|---|---|
| Assertion always holds | `assert indexFloat >= 1.0;` |
| Loop Invariant (derived) | `1.0 <= indexFloat` |
| Procedure Contract (derived) | `Modifies: []` |

**Overall Result: All specifications hold — 1 specifications checked, all of them hold.**