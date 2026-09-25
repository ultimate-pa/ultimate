# Example 4: `My_Loop`

Boogie Model: [`my_loop.bpl`](my_loop.bpl)

Source: `../testsuite/gnatprove/tests/R911-014__loop/my_loop.adb`

## Original Ada

    procedure My_Loop is
       Loop_Cond : Boolean := True;
    begin
       while Loop_Cond loop
          Loop_Cond := False;
          pragma Loop_Invariant (True);
          pragma Assert (Loop_Cond); --@ASSERT:FAIL
       end loop;
    end My_Loop;

## Modeling Idea

The Ada source is itself marked as expected to fail (`--@ASSERT:FAIL`). `Loop_Cond` is set to `False` at the start of every iteration, right before it's asserted to be true — so the assert can never hold, and the trivial invariant `True` doesn't help. The Boogie model keeps this exact structure, so Ultimate should find the same failure.

## Results from Ultimate PA

| Type | Description |
|---|---|
| Assertion can be violated | `assert Loop_Cond;`<br>**FailurePath:** `[L5] Loop_Cond := true;` ➔ `[L8] invariant true;` ➔ `[L7] COND TRUE Loop_Cond` ➔ `[L10] Loop_Cond := false;` ➔ `[L11] assert Loop_Cond;` (fails) |
| Not analyzed | `Not analyzed if loop invariant is valid` |

**Overall Result: FAIL confirmed**, in accordance with the `--@ASSERT:FAIL` annotation in the original Ada. Ultimate Automizer outputs a concrete counterexample path showing that the assertion fails in the very first iteration.