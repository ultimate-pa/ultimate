implementation ULTIMATE.init() returns (){
  $Ultimate##0:
    return;
}

implementation ULTIMATE.start() returns (){
    var #t~ret0 : C_INT;

  $Ultimate##0:
    call ULTIMATE.init();
    call #t~ret0 := main();
    return;
}

implementation float_to_bitvec32(f_in : C_FLOAT) returns (bv_out : C_FLOAT){
  $Ultimate##0:
    return;
}

type { :isUnsigned false } { :bitsize 8 } C_CHAR = bv8;
type { :isUnsigned false } { :bitsize 8 } C_SCHAR = bv8;
type { :isUnsigned true } { :bitsize 8 } C_UCHAR = bv8;
type { :isUnsigned false } { :bitsize 16 } C_SHORT = bv16;
type { :isUnsigned true } { :bitsize 16 } C_USHORT = bv16;
type { :isUnsigned false } { :bitsize 32 } C_INT = bv32;
type { :isUnsigned true } { :bitsize 32 } C_UINT = bv32;
type { :isUnsigned false } { :bitsize 32 } C_LONG = bv32;
type { :isUnsigned true } { :bitsize 32 } C_ULONG = bv32;
type { :isUnsigned false } { :bitsize 64 } C_LONGLONG = bv64;
type { :isUnsigned true } { :bitsize 64 } C_ULONGLONG = bv64;
type { :isUnsigned true } { :bitsize 8 } C_BOOL = bv8;
type { :builtin "RoundingMode" } FloatRoundingMode;
const { :builtin "roundNearestTiesToEven" } ~roundNearestTiesToEven : FloatRoundingMode;
const { :builtin "roundNearestTiesToAway" } ~roundNearestTiesToAway : FloatRoundingMode;
const { :builtin "roundTowardPositive" } ~roundTowardPositive : FloatRoundingMode;
const { :builtin "roundTowardNegative" } ~roundTowardNegative : FloatRoundingMode;
const { :builtin "roundTowardZero" } ~roundTowardZero : FloatRoundingMode;
type { :bitsize 32 } C_FLOAT = bv32;
type { :bitsize 32 } C_DOUBLE = bv32;
type { :bitsize 32 } C_LONGDOUBLE = bv32;
implementation __VERIFIER_assert(#in~cond : C_INT) returns (){
    var ~cond : C_INT;

  $Ultimate##0:
    ~cond := #in~cond;
    goto $Ultimate##1, $Ultimate##2;
  $Ultimate##1:
    assume 0bv32 == ~cond;
    goto ERROR;
  ERROR:
    assert false;
    goto $Ultimate##3;
  $Ultimate##2:
    assume !(0bv32 == ~cond);
    goto $Ultimate##3;
  $Ultimate##3:
    return;
}

implementation main() returns (#res : C_INT){
    var ~f~0 : C_FLOAT;

  $Ultimate##0:
    ~f~0 := ~convertDOUBLEToFLOAT(~roundNearestTiesToEven, ~to_fp~DOUBLE(~roundNearestTiesToEven, 0.1)[31:0] ++ ~fp.neg~DOUBLE(~to_fp~DOUBLE(~roundNearestTiesToEven, 0.2))[32:31]);
    call __VERIFIER_assert((if ~fp.eq~DOUBLE(~fp~FLOAT(~convertFLOATToDOUBLE(~roundNearestTiesToEven, ~f~0)[32:31], ~convertFLOATToDOUBLE(~roundNearestTiesToEven, ~f~0)[31:23], ~convertFLOATToDOUBLE(~roundNearestTiesToEven, ~f~0)[23:0]), ~fp~FLOAT(~fp.neg~DOUBLE(~to_fp~DOUBLE(~roundNearestTiesToEven, 0.1))[32:31], ~fp.neg~DOUBLE(~to_fp~DOUBLE(~roundNearestTiesToEven, 0.1))[31:23], ~fp.neg~DOUBLE(~to_fp~DOUBLE(~roundNearestTiesToEven, 0.1))[23:0])) then 1bv32 else 0bv32));
    #res := 0bv32;
    return;
}

procedure __VERIFIER_error() returns ();
modifies ;

procedure __VERIFIER_assert(#in~cond : C_INT) returns ();
modifies ;

procedure main() returns (#res : C_INT);
modifies ;

procedure float_to_bitvec32(f_in : C_FLOAT) returns (bv_out : C_FLOAT);
free ensures bv_out == ~fp~FLOAT(f_in[32:31], f_in[31:23], f_in[23:0]);
modifies ;

procedure ULTIMATE.init() returns ();
modifies ;

procedure ULTIMATE.start() returns ();
modifies ;

function { :builtin "fp.neg" } ~fp.neg~DOUBLE(in0 : C_DOUBLE) returns (out : C_DOUBLE);
function { :builtin "to_fp" } { :indices 8,24 } ~convertDOUBLEToFLOAT(in0 : FloatRoundingMode, in1 : C_DOUBLE) returns (out : C_FLOAT);
function { :builtin "to_fp" } { :indices 11,53 } ~convertFLOATToDOUBLE(in0 : FloatRoundingMode, in1 : C_FLOAT) returns (out : C_DOUBLE);
function { :builtin "fp.eq" } ~fp.eq~DOUBLE(in0 : C_DOUBLE, in1 : C_DOUBLE) returns (out : bool);
function { :builtin "fp" } ~fp~FLOAT(in0 : bv1, in1 : bv8, in2 : bv23) returns (out : C_FLOAT);
function { :builtin "to_fp" } { :indices 8,24 } ~to_fp~FLOAT(in0 : FloatRoundingMode, in1 : real) returns (out : C_FLOAT);
function { :builtin "-oo" } { :indices 8,24 } ~Minusoo~FLOAT() returns (out : C_FLOAT);
function { :builtin "+oo" } { :indices 8,24 } ~Plusoo~FLOAT() returns (out : C_FLOAT);
function { :builtin "NaN" } { :indices 8,24 } ~NaN~FLOAT() returns (out : C_FLOAT);
function { :builtin "-zero" } { :indices 8,24 } ~Minuszero~FLOAT() returns (out : C_FLOAT);
function { :builtin "+zero" } { :indices 8,24 } ~Pluszero~FLOAT() returns (out : C_FLOAT);
function { :builtin "fp" } ~fp~DOUBLE(in0 : bv1, in1 : bv11, in2 : bv52) returns (out : C_DOUBLE);
function { :builtin "to_fp" } { :indices 11,53 } ~to_fp~DOUBLE(in0 : FloatRoundingMode, in1 : real) returns (out : C_DOUBLE);
function { :builtin "-oo" } { :indices 11,53 } ~Minusoo~DOUBLE() returns (out : C_DOUBLE);
function { :builtin "+oo" } { :indices 11,53 } ~Plusoo~DOUBLE() returns (out : C_DOUBLE);
function { :builtin "NaN" } { :indices 11,53 } ~NaN~DOUBLE() returns (out : C_DOUBLE);
function { :builtin "-zero" } { :indices 11,53 } ~Minuszero~DOUBLE() returns (out : C_DOUBLE);
function { :builtin "+zero" } { :indices 11,53 } ~Pluszero~DOUBLE() returns (out : C_DOUBLE);
function { :builtin "fp" } ~fp~LONGDOUBLE(in0 : bv1, in1 : bv15, in2 : bv112) returns (out : C_LONGDOUBLE);
function { :builtin "to_fp" } { :indices 15,113 } ~to_fp~LONGDOUBLE(in0 : FloatRoundingMode, in1 : real) returns (out : C_LONGDOUBLE);
function { :builtin "-oo" } { :indices 15,113 } ~Minusoo~LONGDOUBLE() returns (out : C_LONGDOUBLE);
function { :builtin "+oo" } { :indices 15,113 } ~Plusoo~LONGDOUBLE() returns (out : C_LONGDOUBLE);
function { :builtin "NaN" } { :indices 15,113 } ~NaN~LONGDOUBLE() returns (out : C_LONGDOUBLE);
function { :builtin "-zero" } { :indices 15,113 } ~Minuszero~LONGDOUBLE() returns (out : C_LONGDOUBLE);
function { :builtin "+zero" } { :indices 15,113 } ~Pluszero~LONGDOUBLE() returns (out : C_LONGDOUBLE);
function { :builtin "bvadd" } ~bvadd8(in0 : C_CHAR, in1 : C_CHAR) returns (out : C_CHAR);
function { :builtin "bvadd" } ~bvadd16(in0 : C_SHORT, in1 : C_SHORT) returns (out : C_SHORT);
function { :builtin "bvadd" } ~bvadd32(in0 : C_INT, in1 : C_INT) returns (out : C_INT);
function { :builtin "bvadd" } ~bvadd64(in0 : C_LONGLONG, in1 : C_LONGLONG) returns (out : C_LONGLONG);
