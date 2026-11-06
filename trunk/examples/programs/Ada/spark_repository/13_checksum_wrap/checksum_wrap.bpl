function {:builtin "bvand"} ~bvand32(in0: bv32, in1: bv32) returns (out: bv32);
function {:builtin "bvadd"} ~bvadd32(in0: bv32, in1: bv32) returns (out: bv32);
function {:builtin "bvlshr"} ~bvlshr32(in0: bv32, in1: bv32) returns (out: bv32);
function {:builtin "bvuge"} ~bvuge32(in0: bv32, in1: bv32) returns (out: bool);
function {:builtin "bvult"} ~bvult32(in0: bv32, in1: bv32) returns (out: bool);

procedure Wrap(S0: bv32) returns (S: bv32)
  ensures ~bvult32(S, 65536bv32);
{
  S := S0;

  while (~bvuge32(S, 65536bv32))
  {
    S := ~bvadd32(~bvand32(S, 65535bv32), ~bvlshr32(S, 16bv32));
  }

  assert ~bvult32(S, 65536bv32);
}
