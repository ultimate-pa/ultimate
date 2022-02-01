//#Unsafe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

axiom {:array_info "$$v"} {:global} {:elem_width 32} {:source_name "v"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$v: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$v: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$v: bool;

const _WATCHED_OFFSET: bv32;

type functionPtr = bv3;

const $functionId$$_Z13multiplyByTwoPfj: functionPtr;

axiom $functionId$$_Z13multiplyByTwoPfj == 1bv3;

const $functionId$$_Z11divideByTwoPfj: functionPtr;

axiom $functionId$$_Z11divideByTwoPfj == 2bv3;

const $functionId$$_Z3fooPfPFfS_jEj: functionPtr;

axiom $functionId$$_Z3fooPfPFfS_jEj == 3bv3;

const $functionId$$null$: functionPtr;

axiom $functionId$$null$ == 0bv3;

const {:group_id_x} group_id_x$1: bv32;

const {:group_id_x} group_id_x$2: bv32;

const {:group_size_x} group_size_x: bv32;

const {:group_size_y} group_size_y: bv32;

const {:group_size_z} group_size_z: bv32;

const {:local_id_x} local_id_x$1: bv32;

const {:local_id_x} local_id_x$2: bv32;

const {:num_groups_x} num_groups_x: bv32;

const {:num_groups_y} num_groups_y: bv32;

const {:num_groups_z} num_groups_z: bv32;

function FMUL32(bv32, bv32) : bv32;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

function {:builtin "bvult"} BV32_ULT(bv32, bv32) : bool;

procedure {:source_name "multiplyByTwo"} $_Z13multiplyByTwoPfj(_P$1: bool, $v$1: bv32, $tid$1: bv32, _P$2: bool, $v$2: bv32, $tid$2: bv32) returns ($ret$1: bv32, $ret$2: bv32);
  requires _P$1 ==> $v$1 == 0bv32;
  requires _P$2 ==> $v$2 == 0bv32;
  requires BV32_SGT(group_size_x, 0bv32);
  requires BV32_SGT(num_groups_x, 0bv32);
  requires BV32_SGE(group_id_x$1, 0bv32);
  requires BV32_SGE(group_id_x$2, 0bv32);
  requires BV32_SLT(group_id_x$1, num_groups_x);
  requires BV32_SLT(group_id_x$2, num_groups_x);
  requires BV32_SGE(local_id_x$1, 0bv32);
  requires BV32_SGE(local_id_x$2, 0bv32);
  requires BV32_SLT(local_id_x$1, group_size_x);
  requires BV32_SLT(local_id_x$2, group_size_x);
  requires BV32_SGT(group_size_y, 0bv32);
  requires BV32_SGT(num_groups_y, 0bv32);
  requires BV32_SGE(group_id_y$1, 0bv32);
  requires BV32_SGE(group_id_y$2, 0bv32);
  requires BV32_SLT(group_id_y$1, num_groups_y);
  requires BV32_SLT(group_id_y$2, num_groups_y);
  requires BV32_SGE(local_id_y$1, 0bv32);
  requires BV32_SGE(local_id_y$2, 0bv32);
  requires BV32_SLT(local_id_y$1, group_size_y);
  requires BV32_SLT(local_id_y$2, group_size_y);
  requires BV32_SGT(group_size_z, 0bv32);
  requires BV32_SGT(num_groups_z, 0bv32);
  requires BV32_SGE(group_id_z$1, 0bv32);
  requires BV32_SGE(group_id_z$2, 0bv32);
  requires BV32_SLT(group_id_z$1, num_groups_z);
  requires BV32_SLT(group_id_z$2, num_groups_z);
  requires BV32_SGE(local_id_z$1, 0bv32);
  requires BV32_SGE(local_id_z$2, 0bv32);
  requires BV32_SLT(local_id_z$1, group_size_z);
  requires BV32_SLT(local_id_z$2, group_size_z);
  requires group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> local_id_x$1 != local_id_x$2 || local_id_y$1 != local_id_y$2 || local_id_z$1 != local_id_z$2;

implementation {:source_name "multiplyByTwo"} $_Z13multiplyByTwoPfj(_P$1: bool, $v$1: bv32, $tid$1: bv32, _P$2: bool, $v$2: bv32, $tid$2: bv32) returns ($ret$1: bv32, $ret$2: bv32)
{
  var v0$1: bv32;
  var v0$2: bv32;
  var _HAVOC_bv32$1: bv32;
  var _HAVOC_bv32$2: bv32;

  $entry:
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    v0$1 := (if _P$1 then _HAVOC_bv32$1 else v0$1);
    v0$2 := (if _P$2 then _HAVOC_bv32$2 else v0$2);
    $ret$1 := (if _P$1 then FMUL32(v0$1, 1073741824bv32) else $ret$1);
    $ret$2 := (if _P$2 then FMUL32(v0$2, 1073741824bv32) else $ret$2);
    return;
}

procedure {:source_name "divideByTwo"} $_Z11divideByTwoPfj(_P$1: bool, $v$1: bv32, $tid$1: bv32, _P$2: bool, $v$2: bv32, $tid$2: bv32) returns ($ret$1: bv32, $ret$2: bv32);
  requires _P$1 ==> $v$1 == 0bv32;
  requires _P$2 ==> $v$2 == 0bv32;
  requires BV32_SGT(group_size_x, 0bv32);
  requires BV32_SGT(num_groups_x, 0bv32);
  requires BV32_SGE(group_id_x$1, 0bv32);
  requires BV32_SGE(group_id_x$2, 0bv32);
  requires BV32_SLT(group_id_x$1, num_groups_x);
  requires BV32_SLT(group_id_x$2, num_groups_x);
  requires BV32_SGE(local_id_x$1, 0bv32);
  requires BV32_SGE(local_id_x$2, 0bv32);
  requires BV32_SLT(local_id_x$1, group_size_x);
  requires BV32_SLT(local_id_x$2, group_size_x);
  requires BV32_SGT(group_size_y, 0bv32);
  requires BV32_SGT(num_groups_y, 0bv32);
  requires BV32_SGE(group_id_y$1, 0bv32);
  requires BV32_SGE(group_id_y$2, 0bv32);
  requires BV32_SLT(group_id_y$1, num_groups_y);
  requires BV32_SLT(group_id_y$2, num_groups_y);
  requires BV32_SGE(local_id_y$1, 0bv32);
  requires BV32_SGE(local_id_y$2, 0bv32);
  requires BV32_SLT(local_id_y$1, group_size_y);
  requires BV32_SLT(local_id_y$2, group_size_y);
  requires BV32_SGT(group_size_z, 0bv32);
  requires BV32_SGT(num_groups_z, 0bv32);
  requires BV32_SGE(group_id_z$1, 0bv32);
  requires BV32_SGE(group_id_z$2, 0bv32);
  requires BV32_SLT(group_id_z$1, num_groups_z);
  requires BV32_SLT(group_id_z$2, num_groups_z);
  requires BV32_SGE(local_id_z$1, 0bv32);
  requires BV32_SGE(local_id_z$2, 0bv32);
  requires BV32_SLT(local_id_z$1, group_size_z);
  requires BV32_SLT(local_id_z$2, group_size_z);
  requires group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> local_id_x$1 != local_id_x$2 || local_id_y$1 != local_id_y$2 || local_id_z$1 != local_id_z$2;

implementation {:source_name "divideByTwo"} $_Z11divideByTwoPfj(_P$1: bool, $v$1: bv32, $tid$1: bv32, _P$2: bool, $v$2: bv32, $tid$2: bv32) returns ($ret$1: bv32, $ret$2: bv32)
{
  var v0$1: bv32;
  var v0$2: bv32;
  var _HAVOC_bv32$1: bv32;
  var _HAVOC_bv32$2: bv32;

  $entry:
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    v0$1 := (if _P$1 then _HAVOC_bv32$1 else v0$1);
    v0$2 := (if _P$2 then _HAVOC_bv32$2 else v0$2);
    $ret$1 := (if _P$1 then FMUL32(v0$1, 1056964608bv32) else $ret$1);
    $ret$2 := (if _P$2 then FMUL32(v0$2, 1056964608bv32) else $ret$2);
    return;
}

procedure {:source_name "foo"} ULTIMATE.start($f: functionPtr, $size: bv32);
  requires !_READ_HAS_OCCURRED_$$v && !_WRITE_HAS_OCCURRED_$$v && !_ATOMIC_HAS_OCCURRED_$$v;
  requires BV32_SGT(group_size_x, 0bv32);
  requires BV32_SGT(num_groups_x, 0bv32);
  requires BV32_SGE(group_id_x$1, 0bv32);
  requires BV32_SGE(group_id_x$2, 0bv32);
  requires BV32_SLT(group_id_x$1, num_groups_x);
  requires BV32_SLT(group_id_x$2, num_groups_x);
  requires BV32_SGE(local_id_x$1, 0bv32);
  requires BV32_SGE(local_id_x$2, 0bv32);
  requires BV32_SLT(local_id_x$1, group_size_x);
  requires BV32_SLT(local_id_x$2, group_size_x);
  requires BV32_SGT(group_size_y, 0bv32);
  requires BV32_SGT(num_groups_y, 0bv32);
  requires BV32_SGE(group_id_y$1, 0bv32);
  requires BV32_SGE(group_id_y$2, 0bv32);
  requires BV32_SLT(group_id_y$1, num_groups_y);
  requires BV32_SLT(group_id_y$2, num_groups_y);
  requires BV32_SGE(local_id_y$1, 0bv32);
  requires BV32_SGE(local_id_y$2, 0bv32);
  requires BV32_SLT(local_id_y$1, group_size_y);
  requires BV32_SLT(local_id_y$2, group_size_y);
  requires BV32_SGT(group_size_z, 0bv32);
  requires BV32_SGT(num_groups_z, 0bv32);
  requires BV32_SGE(group_id_z$1, 0bv32);
  requires BV32_SGE(group_id_z$2, 0bv32);
  requires BV32_SLT(group_id_z$1, num_groups_z);
  requires BV32_SLT(group_id_z$2, num_groups_z);
  requires BV32_SGE(local_id_z$1, 0bv32);
  requires BV32_SGE(local_id_z$2, 0bv32);
  requires BV32_SLT(local_id_z$1, group_size_z);
  requires BV32_SLT(local_id_z$2, group_size_z);
  requires group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> local_id_x$1 != local_id_x$2 || local_id_y$1 != local_id_y$2 || local_id_z$1 != local_id_z$2;

implementation {:source_name "foo"} ULTIMATE.start($f: functionPtr, $size: bv32)
{
  var v0$1: bv32;
  var v0$2: bv32;
  var v1$1: bool;
  var v1$2: bool;
  var v2$1: bv32;
  var v2$2: bv32;
  var v3$1: bv32;
  var v3$2: bv32;
  var p0$1: bool;
  var p0$2: bool;
  var p1$1: bool;
  var p1$2: bool;
  var p2$1: bool;
  var p2$2: bool;
  var p3$1: bool;
  var p3$2: bool;
  var p4$1: bool;
  var p4$2: bool;
  var p5$1: bool;
  var p5$2: bool;

  $entry:
    v0$1 := BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1);
    v0$2 := BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2);
    v1$1 := BV32_ULT(v0$1, $size);
    v1$2 := BV32_ULT(v0$2, $size);
    p0$1 := false;
    p0$2 := false;
    p1$1 := false;
    p1$2 := false;
    p2$1 := false;
    p2$2 := false;
    p3$1 := false;
    p3$2 := false;
    p4$1 := false;
    p4$2 := false;
    p5$1 := false;
    p5$2 := false;
    p0$1 := (if v1$1 then v1$1 else p0$1);
    p0$2 := (if v1$2 then v1$2 else p0$2);
    p1$1 := (if p0$1 && $f == $functionId$$_Z13multiplyByTwoPfj then $f == $functionId$$_Z13multiplyByTwoPfj else p1$1);
    p1$2 := (if p0$2 && $f == $functionId$$_Z13multiplyByTwoPfj then $f == $functionId$$_Z13multiplyByTwoPfj else p1$2);
    p2$1 := (if p0$1 && $f != $functionId$$_Z13multiplyByTwoPfj then $f != $functionId$$_Z13multiplyByTwoPfj else p2$1);
    p2$2 := (if p0$2 && $f != $functionId$$_Z13multiplyByTwoPfj then $f != $functionId$$_Z13multiplyByTwoPfj else p2$2);
    call v2$1, v2$2 := $_Z13multiplyByTwoPfj(p1$1, 0bv32, v0$1, p1$2, 0bv32, v0$2);
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z13multiplyByTwoPfj"} true;
    p3$1 := (if p2$1 && $f == $functionId$$_Z11divideByTwoPfj then $f == $functionId$$_Z11divideByTwoPfj else p3$1);
    p3$2 := (if p2$2 && $f == $functionId$$_Z11divideByTwoPfj then $f == $functionId$$_Z11divideByTwoPfj else p3$2);
    p4$1 := (if p2$1 && $f != $functionId$$_Z11divideByTwoPfj then $f != $functionId$$_Z11divideByTwoPfj else p4$1);
    p4$2 := (if p2$2 && $f != $functionId$$_Z11divideByTwoPfj then $f != $functionId$$_Z11divideByTwoPfj else p4$2);
    call v2$1, v2$2 := $_Z11divideByTwoPfj(p3$1, 0bv32, v0$1, p3$2, 0bv32, v0$2);
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z11divideByTwoPfj"} true;
    assert {:bad_pointer_access} {:sourceloc_num 8} {:thread 1} p4$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 8} {:thread 2} p4$2 ==> false;
    call v3$1, v3$2 := $_Z13multiplyByTwoPfj(p0$1, 0bv32, v0$1, p0$2, 0bv32, v0$2);
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z13multiplyByTwoPfj"} true;
    return;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 1024bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 1bv32 then 1bv1 else 0bv1) != 0bv1;

const {:local_id_y} local_id_y$1: bv32;

const {:local_id_y} local_id_y$2: bv32;

const {:local_id_z} local_id_z$1: bv32;

const {:local_id_z} local_id_z$2: bv32;

const {:group_id_y} group_id_y$1: bv32;

const {:group_id_y} group_id_y$2: bv32;

const {:group_id_z} group_id_z$1: bv32;

const {:group_id_z} group_id_z$2: bv32;

const _WATCHED_VALUE_$$v: bv32;

procedure {:inline 1} _LOG_READ_$$v(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$v;

implementation {:inline 1} _LOG_READ_$$v(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$v := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$v == _value then true else _READ_HAS_OCCURRED_$$v);
    return;
}

procedure _CHECK_READ_$$v(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$v && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$v);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$v && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$v: bool;

procedure {:inline 1} _LOG_WRITE_$$v(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$v, _WRITE_READ_BENIGN_FLAG_$$v;

implementation {:inline 1} _LOG_WRITE_$$v(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$v := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$v == _value then true else _WRITE_HAS_OCCURRED_$$v);
    _WRITE_READ_BENIGN_FLAG_$$v := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$v == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$v);
    return;
}

procedure _CHECK_WRITE_$$v(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$v && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$v != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$v && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$v != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$v && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$v(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$v;

implementation {:inline 1} _LOG_ATOMIC_$$v(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$v := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$v);
    return;
}

procedure _CHECK_ATOMIC_$$v(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$v && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$v && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$v(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$v;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$v(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$v := (if _P && _WRITE_HAS_OCCURRED_$$v && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$v);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
