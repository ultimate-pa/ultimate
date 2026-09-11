# Example 2: `Sum`

Boogie Model: [`sum.bpl`](sum.bpl)

Source: `../testsuite/gnatprove/tests/O512-022__power_and_sum/power_and_sum.adb`

## Original Ada

```ada
procedure Sum(N : in Positive; Result: out Positive) is
   I : Positive := 1;
   TotalSum : Natural := 0;
begin
   while I <= N loop
      pragma Loop_Invariant (2*TotalSum = I*(I-1));

      TotalSum := TotalSum + I;
      I := I + 1;
   end loop;
   pragma Assert (2*TotalSum = N*(N+1));
   Result := TotalSum;
end Sum;
```

## Modeling Idea

The classic Gauss sum: `Sum` adds up `1 + 2 + ... + N`, and checks the closed form `2*TotalSum = N*(N+1)` at the end. `N`, `I`, `TotalSum`, `Result` are plain Boogie `int`s; `Positive`/`Natural` become the precondition `N >= 1`. The closing `assert` is also added as the procedure's `ensures`, since it holds whenever `Sum` returns. The 32-bit overflow check is not modeled, same as elsewhere in this set.

## Results from Ultimate PA

| Type | Description |
|---|---|
| Assertion always holds | `assert 2 * TotalSum == N * (N + 1);` |
| Procedure postcondition always holds | `ensures 2 * Result == N * (N + 1);` |
| Loop Invariant (derived) | `(N + N * N == 2 * TotalSum \|\| I < N + 1) && I + 2 * TotalSum == I * I` |
| Procedure Contract (derived) | `Modifies: []` |

**Overall Result: All specifications hold — 2 specifications checked, all of them hold.**
