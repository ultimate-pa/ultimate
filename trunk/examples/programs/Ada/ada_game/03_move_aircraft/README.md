# Idea 3: `Move_Aircraft`
Boogie Model: [`move_aircraft.bpl`](move_aircraft.bpl)

## Original Ada

The aircraft movement part from the Ada main loop (actions `'N'` for forward movement, `'C'` for climb). The recurring movement block is isolated and modeled as its own procedure.

## Modeling Idea

- **`Move_Aircraft_Forward`** — Forward movement by `Jet_Vel` steps (action `'N'`).
- **`Move_Aircraft_Climb`** — Climb by one row plus subsequent forward movement (action `'C'`); for `'D'` (descent) the structure would be identical, only with `Jet_Row - 1` and the condition `Jet_Row > 1`.

The proposed specification is verified to ensure that the grid arrays are never accessed out-of-bounds, even at maximum speed (`Jet_Vel = 3`).

## Results from Ultimate PA

| Type | Description |
|---|---|
| Assertion always holds | `assert Jet_Row >= 1 && Jet_Row <= ROWS;` (after the climb `if`) |
| Assertion always holds | `assert Jet_Row >= 1 && Jet_Row <= ROWS;` (in the forward loop) |
| Assertion always holds | `assert Jet_Col >= 1 && Jet_Col <= COLS;` (in the forward loop) |
| Procedure postcondition always holds | `ensures Jet_Col >= 1 && Jet_Col <= COLS + 1;` — applies to both procedures |
| Loop Invariant (derived, forward loop in `Move_Aircraft_Climb`) | `(((((step <= Jet_Vel && Jet_Row <= ROWS) && 1 <= Jet_Col) && 2 <= Jet_Row) && 1 <= Jet_Vel) && Jet_Col <= 20) \|\| ((((Jet_Row <= ROWS && 2 <= Jet_Col) && 2 <= Jet_Row) && 1 <= Jet_Vel) && Jet_Col <= COLS)` |
| Procedure Contract (derived) | `Move_Aircraft_Climb` — `Modifies: [Jet_Row, Jet_Col]` |

**Overall Result: All specifications hold — 5 specifications checked, all of them hold.**

### Plausibility Check of the Derived Invariant

A notable part is the subterm `2 <= Jet_Row` in both disjuncts. It is correct: `ROWS == 5`, and before the forward loop either `Jet_Row < ROWS` applies → `Jet_Row` is increased to at least `2`, or `Jet_Row == ROWS == 5` remains unchanged (`5 >= 2`). Thus, `Jet_Row ∈ [2, 5]` is valid in any case at this point.