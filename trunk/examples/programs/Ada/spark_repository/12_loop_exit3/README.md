# Example 12: `Loop_Exit3`

Boogie Model: [`loop_exit3.bpl`](loop_exit3.bpl) (1:1 translation) and [`loop_exit3_modified.bpl`](loop_exit3_modified.bpl) (with the assert fixed, see below)

Source: `../testsuite/gnatprove/tests/S613-026__loop_exit/loop_exit3.adb`

## Original Ada

```ada
procedure Loop_Exit3 is
   X : Integer := 1;
   Y : Boolean := False;
begin
   while X > 0 loop
      Y := False;
      while X > 0 loop
         if X > 0 then
            X := 0;
            Y := True;
            exit;
         end if;
         for I in 1 .. 3 loop
            null;
         end loop;
      end loop;
      pragma Assert (Y = False);  --  @ASSERT:FAIL
   end loop;
end Loop_Exit3;
```

## Modeling Idea

Nested loops plus `exit`, a step up in structure from the previous
examples: an outer `while`, an inner `while` containing an `if`/`exit`
and a dead `for` loop. Boogie's `break;` maps directly onto Ada's `exit;`
(breaks the nearest enclosing loop, i.e. the inner `while`). The inner
`if X > 0 then ... end if` is followed by a `for I in 1 .. 3 loop null;
end loop;` that can only be reached when the `if` condition is false —
but the `if` condition is identical to the loop guard just entered, so
it is always true and the `for` loop is unreachable dead code. It is
kept in the model (as a small bounded `while`) purely for structural
fidelity, even though it has no effect.

`X`, `Y`, `I` are plain `int`/`bool`. No `pragma Loop_Invariant` exists
in the source at all — this isn't a case of "the given invariant is too
weak", there simply isn't one.

## Results from Ultimate PA

### `loop_exit3.bpl`

Ultimate proves this incorrect immediately, with
a concrete, minimal counterexample:

    X := 1; Y := false;
    COND TRUE  X > 0
    Y := false;
    COND TRUE  X > 0
    COND TRUE  X > 0
    X := 0; Y := true;
    assert Y == false;   -- Y == true, fails

Since `X` starts at `1`, the outer loop is entered, the inner loop is
entered, its `if X > 0` is trivially true on the very first pass (same
condition as the just-checked loop guard), so `Y` is unconditionally set
to `true` before `exit` — the `pragma Assert (Y = False)` right after
the inner loop can never hold on any execution. This matches the
`@ASSERT:FAIL` annotation exactly, and Ultimate finds it without any
loop unrolling search.

**Comparison with GNATprove**

    loop_exit3.adb:17:22: high: assertion might fail (e.g. when Y = True)
       [possible fix: loop at line 7 should mention Y in a loop invariant]
       [provers gave up before completing the proof]

- GNATprove's own counterexample here (`Y = True`) already matches a
  real reachable state. But GNATprove still only reports `high: might fail` — a *possibility*,
  not a definitive verdict and its "possible fix" (add a loop
  invariant mentioning `Y`) is not actionable: no invariant can make an
  always-false assertion provable, because the assertion is genuinely
  false on every execution. GNATprove has no way to say "this is not a
  weak-invariant problem, this is a bug" — `high`/`might fail` looks the
  same in both cases.
- Ultimate returns a complete, checkable execution trace

### `loop_exit3_modified.bpl`

The final assert is changed, from `assert Y == false;` to
`assert Y == true;`.

| Type | Description |
|---|---|
| Assertion always holds | `assert Y == true;` |
| Loop Invariant (derived, outer loop) | `0 < X` |
| Loop Invariant (derived, dead inner `for`) | `false` |
| Procedure Contract (derived) | `Modifies: []` |

**Overall Result: All specifications hold — 1 specification checked, it holds.**