# Idea 2: `Initialize_Grid`

Boogie Model: [`initialize_grid.bpl`](initialize_grid.bpl)

## Original Ada

In Ada, two nested `for` loops iterate over the grid to reset it
(all fields `Danger := False`).

## Modeling Idea

Two nested `while` loops over rows (`r`) and columns (`c`), which set
`Grid_Danger[r, c]` to `false` for each field.

## Results from Ultimate PA

| Type | Description |
|---|---|
| Assertion always holds | `assert r >= 1 && r <= ROWS;` |
| Assertion always holds | `assert c >= 1 && c <= COLS;` |
| Loop Invariant (derived, outer loop over `r`) | `0 < r` |
| Loop Invariant (derived, inner loop over `c`) | `((1 <= r && r <= ROWS) && 2 <= c) \|\| ((c == 1 && 1 <= r) && r <= ROWS)` |
| Procedure Contract (derived) | `Modifies: [Grid_Danger]` |

**Overall Result: All specifications hold — 2 specifications checked, all of them hold.**

### Plausibility Check of the Derived Invariants

Both are logically correct and sufficient:

- **Outer Invariant `0 < r`** is weakly formulated but sufficient: within the loop body, the loop condition `r <= ROWS` also applies, so together it is exactly `1 <= r <= ROWS` — exactly what `assert r >= 1 && r <= ROWS` needs.
- **Inner Invariant** states: `r` is always in `[1, ROWS]`, and `c` is either `1` (loop start) or `≥ 2`. Together with the loop condition `c <= COLS`, it follows that `1 <= c <= COLS`, which is sufficient for `assert c >= 1 && c <= COLS`.