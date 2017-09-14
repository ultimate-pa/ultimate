//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "v"} {:global} $$v: [bv32]bv32;

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

const $functionId$$_Z3fooPfj: functionPtr;

axiom $functionId$$_Z3fooPfj == 3bv3;

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

function {:builtin "bvor"} BV32_OR(bv32, bv32) : bv32;

function {:builtin "bvudiv"} BV32_UDIV(bv32, bv32) : bv32;

function {:builtin "zero_extend 31"} BV1_ZEXT32(bv1) : bv32;

procedure {:source_name "multiplyByTwo"} $_Z13multiplyByTwoPfj($v: bv32, $index$1: bv32, $index$2: bv32);
  requires (if BV32_MUL($v, 4bv32) == 0bv32 then 1bv1 else 0bv1) != 0bv1;
  requires (if $index$1 == BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1) then 1bv1 else 0bv1) != 0bv1;
  requires (if $index$2 == BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2) then 1bv1 else 0bv1) != 0bv1;
  requires (if _READ_HAS_OCCURRED_$$v ==> BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32) == $index$1 then 1bv1 else 0bv1) != 0bv1;
  requires (if _WRITE_HAS_OCCURRED_$$v ==> BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32) == $index$1 then 1bv1 else 0bv1) != 0bv1;
  requires $v == 0bv32;
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
  modifies _READ_HAS_OCCURRED_$$v, _WRITE_HAS_OCCURRED_$$v, _WRITE_READ_BENIGN_FLAG_$$v, _WRITE_READ_BENIGN_FLAG_$$v;
  ensures (if _READ_HAS_OCCURRED_$$v ==> BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32) == $index$1 then 1bv1 else 0bv1) != 0bv1;
  ensures (if _WRITE_HAS_OCCURRED_$$v ==> BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32) == $index$1 then 1bv1 else 0bv1) != 0bv1;

implementation {:source_name "multiplyByTwo"} $_Z13multiplyByTwoPfj($v: bv32, $index$1: bv32, $index$2: bv32)
{
  var v0$1: bv32;
  var v0$2: bv32;

  $entry:
    call _LOG_READ_$$v(true, BV32_ADD($v, $index$1), $$v[BV32_ADD($v, $index$1)]);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 7} true;
    call _CHECK_READ_$$v(true, BV32_ADD($v, $index$2), $$v[BV32_ADD($v, $index$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$v"} true;
    v0$1 := $$v[BV32_ADD($v, $index$1)];
    v0$2 := $$v[BV32_ADD($v, $index$2)];
    call _LOG_WRITE_$$v(true, BV32_ADD($v, $index$1), FMUL32(v0$1, 1073741824bv32), $$v[BV32_ADD($v, $index$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$v(true, BV32_ADD($v, $index$2));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 8} true;
    call _CHECK_WRITE_$$v(true, BV32_ADD($v, $index$2), FMUL32(v0$2, 1073741824bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$v"} true;
    $$v[BV32_ADD($v, $index$1)] := FMUL32(v0$1, 1073741824bv32);
    $$v[BV32_ADD($v, $index$2)] := FMUL32(v0$2, 1073741824bv32);
    return;
}

procedure {:source_name "divideByTwo"} $_Z11divideByTwoPfj($v: bv32, $index$1: bv32, $index$2: bv32);
  requires (if BV32_MUL($v, 4bv32) == 0bv32 then 1bv1 else 0bv1) != 0bv1;
  requires (if $index$1 == BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1) then 1bv1 else 0bv1) != 0bv1;
  requires (if $index$2 == BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2) then 1bv1 else 0bv1) != 0bv1;
  requires (if _READ_HAS_OCCURRED_$$v ==> BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32) == $index$1 then 1bv1 else 0bv1) != 0bv1;
  requires (if _WRITE_HAS_OCCURRED_$$v ==> BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32) == $index$1 then 1bv1 else 0bv1) != 0bv1;
  requires $v == 0bv32;
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
  modifies _READ_HAS_OCCURRED_$$v, _WRITE_HAS_OCCURRED_$$v, _WRITE_READ_BENIGN_FLAG_$$v, _WRITE_READ_BENIGN_FLAG_$$v;
  ensures (if _READ_HAS_OCCURRED_$$v ==> BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32) == $index$1 then 1bv1 else 0bv1) != 0bv1;
  ensures (if _WRITE_HAS_OCCURRED_$$v ==> BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32) == $index$1 then 1bv1 else 0bv1) != 0bv1;

implementation {:source_name "divideByTwo"} $_Z11divideByTwoPfj($v: bv32, $index$1: bv32, $index$2: bv32)
{
  var v0$1: bv32;
  var v0$2: bv32;

  $entry:
    call _LOG_READ_$$v(true, BV32_ADD($v, $index$1), $$v[BV32_ADD($v, $index$1)]);
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 16} true;
    call _CHECK_READ_$$v(true, BV32_ADD($v, $index$2), $$v[BV32_ADD($v, $index$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$v"} true;
    v0$1 := $$v[BV32_ADD($v, $index$1)];
    v0$2 := $$v[BV32_ADD($v, $index$2)];
    call _LOG_WRITE_$$v(true, BV32_ADD($v, $index$1), FMUL32(v0$1, 1056964608bv32), $$v[BV32_ADD($v, $index$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$v(true, BV32_ADD($v, $index$2));
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 17} true;
    call _CHECK_WRITE_$$v(true, BV32_ADD($v, $index$2), FMUL32(v0$2, 1056964608bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$v"} true;
    $$v[BV32_ADD($v, $index$1)] := FMUL32(v0$1, 1056964608bv32);
    $$v[BV32_ADD($v, $index$2)] := FMUL32(v0$2, 1056964608bv32);
    return;
}

procedure {:source_name "foo"} ULTIMATE.start($i: bv32);
  requires (if BV32_OR(BV1_ZEXT32((if $i == 1bv32 then 1bv1 else 0bv1)), BV1_ZEXT32((if $i == 2bv32 then 1bv1 else 0bv1))) != 0bv32 then 1bv1 else 0bv1) != 0bv1;
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
  modifies _READ_HAS_OCCURRED_$$v, _WRITE_HAS_OCCURRED_$$v, _WRITE_READ_BENIGN_FLAG_$$v, _WRITE_READ_BENIGN_FLAG_$$v;

implementation {:source_name "foo"} ULTIMATE.start($i: bv32)
{
  var $f.1: functionPtr;
  var $f.0: functionPtr;
  var v0: bool;
  var v1: bool;
  var v2$1: bv32;
  var v2$2: bv32;

  $entry:
    v0 := $i == 1bv32;
    goto $truebb, $falsebb;

  $falsebb:
    assume {:partition} !v0;
    v1 := $i == 2bv32;
    goto $truebb0, $falsebb0;

  $falsebb0:
    assume {:partition} !v1;
    $f.0 := $functionId$$null$;
    goto $if.end;

  $if.end:
    $f.1 := $f.0;
    goto $if.end7;

  $if.end7:
    v2$1 := BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1);
    v2$2 := BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2);
    goto anon4_Then, anon4_Else;

  anon4_Else:
    assume {:partition} $f.1 != $functionId$$_Z13multiplyByTwoPfj;
    goto anon5_Then, anon5_Else;

  anon5_Else:
    assume {:partition} $f.1 != $functionId$$_Z11divideByTwoPfj;
    assert {:bad_pointer_access} {:sourceloc_num 26} {:thread 1} false;
    goto anon3;

  anon3:
    return;

  anon5_Then:
    assume {:partition} $f.1 == $functionId$$_Z11divideByTwoPfj;
    call $_Z11divideByTwoPfj(0bv32, v2$1, v2$2);
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z11divideByTwoPfj"} true;
    goto anon3;

  anon4_Then:
    assume {:partition} $f.1 == $functionId$$_Z13multiplyByTwoPfj;
    call $_Z13multiplyByTwoPfj(0bv32, v2$1, v2$2);
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z13multiplyByTwoPfj"} true;
    goto anon3;

  $truebb0:
    assume {:partition} v1;
    $f.0 := $functionId$$_Z11divideByTwoPfj;
    goto $if.end;

  $truebb:
    assume {:partition} v0;
    $f.1 := $functionId$$_Z13multiplyByTwoPfj;
    goto $if.end7;
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
