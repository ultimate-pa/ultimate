# Formal Verification of Selected Elements from `Ada_Game` and Examples from the `SPARK Repository` with Ultimate Automizer

This folder documents a pipeline with which selected excerpts from two source repositories are formally verified:

```
Ada Code (Original)  →  Boogie PL Model (.bpl)  →  Ultimate Automizer
```

`Ada_Game` contains hardly any specifications; the Ada examples from the `SPARK Repository` code sometimes bring their own `Pre`/`Post`/`Global` specifications, which serve as a reference when translating to Boogie and are compared against the `requires`/`ensures` clauses.

## Selection Criterion

Not all code is modeled. Excerpts are specifically selected from the original code (both from `Ada_Game` and the examples from the `SPARK Repository`), which:

- contain assertions and loops,
- and use no strings if possible.

## Structure

The examples are initially separated by source repository, then per investigated idea in a dedicated subfolder with two files:

```
Ada/
├── README.md
├── ada_game/
│   ├── 01_adjust_orbit/
│   │   ├── README.md
│   │   └── adjust_orbit.bpl
│   ├── 02_initialize_grid/
│   └── 03_move_aircraft/
└── spark_repository/
    └── ...
```

| File | Purpose |
|---|---|
| `README.md` | Original excerpt in Ada, description of the modeling, results from Ultimate |
| `*.bpl` | Standalone executable Boogie model, can be loaded directly into Ultimate Automizer |

The Boogie code is only located in the `.bpl` file and is not duplicated in the respective `README.md`.

## Overview of the Examples

### `Ada_Game`

| # | Folder | Procedure | Verified Property |
|---|---|---|---|
| 1 | [`ada_game/01_adjust_orbit`](ada_game/01_adjust_orbit/README.md) | `Adjust_Orbit` | Value range (Low Earth Orbit 160–2000 km, Speed > 0), frame condition |
| 2 | [`ada_game/02_initialize_grid`](ada_game/02_initialize_grid/README.md) | Grid setup | Nested loop bounds (`r`/`c` within grid range) |
| 3 | [`ada_game/03_move_aircraft`](ada_game/03_move_aircraft/README.md) | `Move_Aircraft` | No out-of-bounds accesses |

### `SPARK Repository`

| # | Folder | Procedure | Verified Property |
|---|---|---|---|
| 1 | [`01_binary_search_full`](01_binary_search_full/README.md) | `Binary_Search.Search` (full, pointwise invariant) | Found position is correct / not found element does not occur anywhere |
| 2 | [`02_power_and_sum`](02_power_and_sum/README.md) | `Sum` | `2 * Result == N * (N + 1)` (Gauss sum closed form) |
| 3 | [`03_loopvar`](03_loopvar/README.md) | `Loopvar` | `X > 0` in the loop body |
| 4 | [`04_buggy_loop_invariant`](04_buggy_loop_invariant/README.md) | `My_Loop` | `Loop_Cond` in the body (counterexample) |
| 5 | [`05_pi_euler_harmonic`](05_pi_euler_harmonic/README.md) | `Pi_Euler` | `Index >= 1` before division |
| 6 | [`06_pi_euler_range_constrained`](06_pi_euler_range_constrained/README.md) | `Pi_Euler_2` | `Index_Float >= 1.0` before division |
| 7 | [`07_functional_set_find`](07_functional_set_find/README.md) | `My_Find` (from `use_ordered_sets.adb`) | Searched element does not occur before the found position |
| 8 | [`08_const_in_loop`](08_const_in_loop/README.md) | `Const_In_Loop` | `V1 == 1` always, despite `V1` only being written on one specific iteration of a "constant" re-declared each loop pass |
| 9 | [`09_functional_list_add1`](09_functional_list_add1/README.md) | `Add_1` (from `use_lists.adb`) | `L2` is `L1` element-wise saturating incremented |
| 10 | [`10_functional_set_move_split`](10_functional_set_move_split/README.md) | `Move_2` (from `use_ordered_sets.adb`) | `S2` is a copy of the original `S1` after the loop |