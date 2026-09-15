type {:builtin "FloatingPoint"} {:indices 11, 53} double;
type {:builtin "RoundingMode"} RM;

const {:builtin "roundNearestTiesToEven"} RNE: RM;

// Integer'Last for a 32-bit signed Ada Integer (Positive is a subtype of Integer)
const INT_MAX: bv32;
axiom INT_MAX == 2147483647bv32;

function {:builtin "bvadd"} ~bvadd32(in0: bv32, in1: bv32) returns (out: bv32);
function {:builtin "bvslt"} ~bvslt32(in0: bv32, in1: bv32) returns (out: bool);
function {:builtin "bvsge"} ~bvsge32(in0: bv32, in1: bv32) returns (out: bool);

function {:builtin "to_fp"} {:indices 11, 53} ~IntToDouble(rm: RM, x: bv32) returns (out: double);
function {:builtin "to_fp"} {:indices 11, 53} ~RealToDouble(rm: RM, r: real) returns (out: double);

function {:builtin "fp.div"} ~fp_div(rm: RM, in0: double, in1: double) returns (out: double);
function {:builtin "fp.add"} ~fp_add(rm: RM, in0: double, in1: double) returns (out: double);
function {:builtin "fp.geq"} ~fp_geq(in0: double, in1: double) returns (out: bool);

function Inv(rm: RM, x: double) returns (double)
{
  ~fp_div(rm, ~RealToDouble(rm, 1.0), x)
}

procedure PiEuler() returns (pi: double)
{
  var index: bv32;
  var erreur: double;

  pi := ~RealToDouble(RNE, 0.0);
  index := 1bv32;
  erreur := ~RealToDouble(RNE, 1.0);

  while (~fp_geq(erreur, ~RealToDouble(RNE, 0.00000008)))
  {
    assert ~bvsge32(index, 1bv32);
    assert ~fp_geq(~IntToDouble(RNE, index), ~RealToDouble(RNE, 1.0));

    erreur := Inv(RNE, ~IntToDouble(RNE, index));
    pi := ~fp_add(RNE, pi, erreur);

    // Ada raises Constraint_Error on Integer overflow: model the runtime check
    // performed by "Index + 1" before the increment actually happens.
    assert ~bvslt32(index, INT_MAX);
    index := ~bvadd32(index, 1bv32);
  }
}
