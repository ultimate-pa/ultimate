# Example 11: `Align_To_Word`

Boogie Model: [`align_to_word.bpl`](align_to_word.bpl) (1:1 translation) and [`align_to_word_modified.bpl`](align_to_word_modified.bpl) (with one extra assert, see below)

Source: `../testsuite/gnatprove/tests/ipstack/src/core/aip-checksum.adb` (procedure `Sum_Chunk`)

## Original Ada

```ada
while Data_I mod 4 /= 0 and then Remain >= 2 loop
   Result := Result + Get_Word;
   Data_I := Data_I + 2;
   Remain := Remain - 2;
end loop;
```

This is the word-alignment part of `Sum_Chunk` from AdaCore's IPStack (a checksum routine): it advances a memory pointer `Data_I` two bytes at a time until it's word-aligned (`Data_I mod 4 = 0`) or the remaining length runs out.

## Modeling Idea

`Get_Word`/`Result` (memory reads) aren't relevant to the alignment property, so only the arithmetic on `Data_I`/`Remain` is kept. Unlike the `mod`/`div` style used elsewhere in this set, this example uses real 32-bit bitvector arithmetic (`bv32`) instead of mathematical integers: `Data_I mod 4` becomes the bitwise `Data_I and 3bv32` — the two lowest bits — mirroring what the actual machine instruction does for an alignment check. `Data_I` is guaranteed even on entry (from the preceding odd-byte handling in the original, not shown here), which is added as a precondition.

`align_to_word.bpl` is the faithful 1:1 translation — just the original loop and its post-loop assert. That assert alone follows directly from the loop guard being false at exit, so it didn't actually need a loop invariant to prove (see Results below).

`align_to_word_modified.bpl` adds one assert inside the loop body, not present in the original Ada, checking that `Data_I` stays even on every iteration. That one does require Ultimate to find and maintain a real invariant across iterations, so it's kept as a separate file rather than changing the 1:1 translation.

## Results from Ultimate PA

### `align_to_word.bpl` (1:1)

| Type | Description |
|---|---|
| Assertion always holds | `assert ~bvand32(Data_I, 3bv32) == 0bv32 \|\| ~bvult32(Remain, 2bv32);` |
| Procedure postcondition always holds | `ensures ~bvand32(Data_I, 3bv32) == 0bv32 \|\| ~bvult32(Remain, 2bv32);` |
| Procedure Contract (derived) | `Modifies: []` |

**Overall Result: All specifications hold — 2 specifications checked, all of them hold.**

### `align_to_word_modified.bpl`

| Type | Description |
|---|---|
| Assertion always holds | `assert ~bvand32(Data_I, 1bv32) == 0bv32;` (inside the loop) |
| Assertion always holds | `assert ~bvand32(Data_I, 3bv32) == 0bv32 \|\| ~bvult32(Remain, 2bv32);` (after the loop) |
| Procedure postcondition always holds | `ensures ~bvand32(Data_I, 3bv32) == 0bv32 \|\| ~bvult32(Remain, 2bv32);` |
| Loop Invariant (derived) | `~bvand32(1bv32, Data_I) == 0bv32 && 0bv32 == ~bvand32(1bv32, Data_I0)` |
| Procedure Contract (derived) | `Modifies: []` |

**Overall Result: All specifications hold — 3 specifications checked, all of them hold.**
