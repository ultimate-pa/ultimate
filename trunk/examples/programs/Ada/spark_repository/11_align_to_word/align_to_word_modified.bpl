function {:builtin "bvand"} ~bvand32(in0: bv32, in1: bv32) returns (out: bv32);
function {:builtin "bvadd"} ~bvadd32(in0: bv32, in1: bv32) returns (out: bv32);
function {:builtin "bvsub"} ~bvsub32(in0: bv32, in1: bv32) returns (out: bv32);
function {:builtin "bvuge"} ~bvuge32(in0: bv32, in1: bv32) returns (out: bool);
function {:builtin "bvult"} ~bvult32(in0: bv32, in1: bv32) returns (out: bool);

procedure Align_To_Word(Data_I0: bv32, Remain0: bv32) returns (Data_I: bv32, Remain: bv32)
  requires ~bvand32(Data_I0, 1bv32) == 0bv32;
  ensures ~bvand32(Data_I, 3bv32) == 0bv32 || ~bvult32(Remain, 2bv32);
{
  Data_I := Data_I0;
  Remain := Remain0;

  while (~bvand32(Data_I, 3bv32) != 0bv32 && ~bvuge32(Remain, 2bv32))
  {
    Data_I := ~bvadd32(Data_I, 2bv32);
    Remain := ~bvsub32(Remain, 2bv32);
    assert ~bvand32(Data_I, 1bv32) == 0bv32;
  }

  assert ~bvand32(Data_I, 3bv32) == 0bv32 || ~bvult32(Remain, 2bv32);
}
