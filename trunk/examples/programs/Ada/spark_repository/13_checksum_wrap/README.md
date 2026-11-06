# Example 13: `Wrap`

Boogie Model: [`checksum_wrap.bpl`](checksum_wrap.bpl) (1:1 translation)

Source: `../testsuite/gnatprove/tests/ipstack/src/core/aip-checksum.adb`
(procedure `Wrap`)

## Original Ada

```ada
procedure Wrap (S : in out M32_T) is
begin
   while S >= 2 ** 16 loop
      S := (S and 16#ffff#) + (S / 2**16);
   end loop;
end Wrap;
```

## Modeling Idea

The procedure repeatedly splits a value into its low 16 bits and everything above, and add them back together, until the result fits in 16 bits.

Since Boogie's native `int` has no bitwise operators, `S` is modeled as a genuine 32-bit bitvector (`bv32`), using Boogie/SMT-LIB bitvector builtins.

## Results from Ultimate PA

| Type | Description |
|---|---|
| Assertion always holds | `assert ~bvult32(S, 65536bv32);` |
| Procedure postcondition always holds | `ensures ~bvult32(S, 65536bv32);` |
| Procedure Contract (derived) | `Modifies: []` |

**Overall Result: All specifications hold — 2 specifications checked, all of them hold.**