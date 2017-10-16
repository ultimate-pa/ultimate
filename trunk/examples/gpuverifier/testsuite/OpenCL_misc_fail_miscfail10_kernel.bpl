//#Unsafe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "h1"} {:global} $$h1: [bv32]bv32;

axiom {:array_info "$$h1"} {:global} {:elem_width 32} {:source_name "h1"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$h1: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$h1: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$h1: bool;

const $arrayId$$h1: arrayId;

axiom $arrayId$$h1 == 1bv3;

var {:source_name "h2"} {:global} $$h2: [bv32]bv32;

axiom {:array_info "$$h2"} {:global} {:elem_width 32} {:source_name "h2"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$h2: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$h2: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$h2: bool;

const $arrayId$$h2: arrayId;

axiom $arrayId$$h2 == 2bv3;

axiom {:array_info "$$foo.l"} {:group_shared} {:elem_width 32} {:source_name "l"} {:source_elem_width 32} {:source_dimensions "256"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$foo.l: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$foo.l: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$foo.l: bool;

const $arrayId$$foo.l: arrayId;

axiom $arrayId$$foo.l == 3bv3;

type ptr = bv32;

type arrayId = bv3;

function {:inline true} MKPTR(base: arrayId, offset: bv32) : ptr
{
  base ++ offset[29:0]
}

function {:inline true} base#MKPTR(p: ptr) : arrayId
{
  p[32:29]
}

function {:inline true} offset#MKPTR(p: ptr) : bv32
{
  0bv3 ++ p[29:0]
}

const $arrayId$$null$: arrayId;

axiom $arrayId$$null$ == 0bv3;

const _WATCHED_OFFSET: bv32;

const {:global_offset_x} global_offset_x: bv32;

const {:global_offset_y} global_offset_y: bv32;

const {:global_offset_z} global_offset_z: bv32;

const {:group_size_x} group_size_x: bv32;

const {:group_size_y} group_size_y: bv32;

const {:group_size_z} group_size_z: bv32;

const {:num_groups_x} num_groups_x: bv32;

const {:num_groups_y} num_groups_y: bv32;

const {:num_groups_z} num_groups_z: bv32;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvult"} BV32_ULT(bv32, bv32) : bool;

procedure {:source_name "foo"} ULTIMATE.start($i: bv32);
  requires !_READ_HAS_OCCURRED_$$h1 && !_WRITE_HAS_OCCURRED_$$h1 && !_ATOMIC_HAS_OCCURRED_$$h1;
  requires !_READ_HAS_OCCURRED_$$h2 && !_WRITE_HAS_OCCURRED_$$h2 && !_ATOMIC_HAS_OCCURRED_$$h2;
  requires !_READ_HAS_OCCURRED_$$foo.l && !_WRITE_HAS_OCCURRED_$$foo.l && !_ATOMIC_HAS_OCCURRED_$$foo.l;
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
  modifies _WRITE_HAS_OCCURRED_$$h1, _WRITE_READ_BENIGN_FLAG_$$h1, _WRITE_READ_BENIGN_FLAG_$$h1, _WRITE_HAS_OCCURRED_$$h2, _WRITE_READ_BENIGN_FLAG_$$h2, _WRITE_READ_BENIGN_FLAG_$$h2, _READ_HAS_OCCURRED_$$h1, _READ_HAS_OCCURRED_$$h2;

implementation {:source_name "foo"} ULTIMATE.start($i: bv32)
{
  var $cond: ptr;
  var $i1.0: bv32;
  var v0: bool;
  var v1: bool;
  var v2$1: bv32;
  var v2$2: bv32;
  var v3$1: bv32;
  var v3$2: bv32;

  $entry:
    v0 := BV32_SGT($i, 0bv32);
    goto $truebb, $falsebb;

  $falsebb:
    assume {:partition} !v0;
    $cond := MKPTR($arrayId$$h2, 0bv32);
    goto $cond.end;

  $cond.end:
    $i1.0 := 0bv32;
    assume {:captureState "loop_entry_state_0_0"} true;
    goto $for.cond;

  $for.cond:
    assume {:captureState "loop_head_state_0"} true;
    assert {:block_sourceloc} {:sourceloc_num 4} true;
    v1 := BV32_ULT($i1.0, 256bv32);
    goto $truebb0, $falsebb0;

  $falsebb0:
    assume {:partition} !v1;
    return;

  $truebb0:
    assume {:partition} v1;
    havoc v2$1, v2$2;
    goto anon8_Then, anon8_Else;

  anon8_Else:
    assume {:partition} base#MKPTR($cond) != $arrayId$$h2;
    goto anon9_Then, anon9_Else;

  anon9_Else:
    assume {:partition} base#MKPTR($cond) != $arrayId$$h1;
    assert {:bad_pointer_access} {:sourceloc_num 9} {:thread 1} false;
    goto anon3;

  anon3:
    goto anon10_Then, anon10_Else;

  anon10_Else:
    assume {:partition} base#MKPTR($cond) != $arrayId$$h2;
    goto anon11_Then, anon11_Else;

  anon11_Else:
    assume {:partition} base#MKPTR($cond) != $arrayId$$h1;
    assert {:bad_pointer_access} {:sourceloc_num 12} {:thread 1} false;
    goto anon7;

  anon7:
    $i1.0 := BV32_ADD($i1.0, 1bv32);
    assume {:captureState "loop_back_edge_state_0_0"} true;
    goto $for.cond;

  anon11_Then:
    assume {:partition} base#MKPTR($cond) == $arrayId$$h1;
    call _LOG_WRITE_$$h1(true, BV32_ADD(offset#MKPTR($cond), $i1.0), BV32_ADD(v3$1, v2$1), $$h1[BV32_ADD(offset#MKPTR($cond), $i1.0)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$h1(true, BV32_ADD(offset#MKPTR($cond), $i1.0));
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 11} true;
    call _CHECK_WRITE_$$h1(true, BV32_ADD(offset#MKPTR($cond), $i1.0), BV32_ADD(v3$2, v2$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$h1"} true;
    $$h1[BV32_ADD(offset#MKPTR($cond), $i1.0)] := BV32_ADD(v3$1, v2$1);
    $$h1[BV32_ADD(offset#MKPTR($cond), $i1.0)] := BV32_ADD(v3$2, v2$2);
    goto anon7;

  anon10_Then:
    assume {:partition} base#MKPTR($cond) == $arrayId$$h2;
    call _LOG_WRITE_$$h2(true, BV32_ADD(offset#MKPTR($cond), $i1.0), BV32_ADD(v3$1, v2$1), $$h2[BV32_ADD(offset#MKPTR($cond), $i1.0)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$h2(true, BV32_ADD(offset#MKPTR($cond), $i1.0));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 10} true;
    call _CHECK_WRITE_$$h2(true, BV32_ADD(offset#MKPTR($cond), $i1.0), BV32_ADD(v3$2, v2$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$h2"} true;
    $$h2[BV32_ADD(offset#MKPTR($cond), $i1.0)] := BV32_ADD(v3$1, v2$1);
    $$h2[BV32_ADD(offset#MKPTR($cond), $i1.0)] := BV32_ADD(v3$2, v2$2);
    goto anon7;

  anon9_Then:
    assume {:partition} base#MKPTR($cond) == $arrayId$$h1;
    call _LOG_READ_$$h1(true, BV32_ADD(offset#MKPTR($cond), $i1.0), $$h1[BV32_ADD(offset#MKPTR($cond), $i1.0)]);
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 8} true;
    call _CHECK_READ_$$h1(true, BV32_ADD(offset#MKPTR($cond), $i1.0), $$h1[BV32_ADD(offset#MKPTR($cond), $i1.0)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$h1"} true;
    v3$1 := $$h1[BV32_ADD(offset#MKPTR($cond), $i1.0)];
    v3$2 := $$h1[BV32_ADD(offset#MKPTR($cond), $i1.0)];
    goto anon3;

  anon8_Then:
    assume {:partition} base#MKPTR($cond) == $arrayId$$h2;
    call _LOG_READ_$$h2(true, BV32_ADD(offset#MKPTR($cond), $i1.0), $$h2[BV32_ADD(offset#MKPTR($cond), $i1.0)]);
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 7} true;
    call _CHECK_READ_$$h2(true, BV32_ADD(offset#MKPTR($cond), $i1.0), $$h2[BV32_ADD(offset#MKPTR($cond), $i1.0)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$h2"} true;
    v3$1 := $$h2[BV32_ADD(offset#MKPTR($cond), $i1.0)];
    v3$2 := $$h2[BV32_ADD(offset#MKPTR($cond), $i1.0)];
    goto anon3;

  $truebb:
    assume {:partition} v0;
    $cond := MKPTR($arrayId$$h1, 0bv32);
    goto $cond.end;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 64bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 64bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_x == 0bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_y == 0bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_z == 0bv32 then 1bv1 else 0bv1) != 0bv1;

const {:local_id_x} local_id_x$1: bv32;

const {:local_id_x} local_id_x$2: bv32;

const {:local_id_y} local_id_y$1: bv32;

const {:local_id_y} local_id_y$2: bv32;

const {:local_id_z} local_id_z$1: bv32;

const {:local_id_z} local_id_z$2: bv32;

const {:group_id_x} group_id_x$1: bv32;

const {:group_id_x} group_id_x$2: bv32;

const {:group_id_y} group_id_y$1: bv32;

const {:group_id_y} group_id_y$2: bv32;

const {:group_id_z} group_id_z$1: bv32;

const {:group_id_z} group_id_z$2: bv32;

const _WATCHED_VALUE_$$h1: bv32;

procedure {:inline 1} _LOG_READ_$$h1(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$h1;

implementation {:inline 1} _LOG_READ_$$h1(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$h1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$h1 == _value then true else _READ_HAS_OCCURRED_$$h1);
    return;
}

procedure _CHECK_READ_$$h1(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$h1 && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$h1);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$h1 && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$h1: bool;

procedure {:inline 1} _LOG_WRITE_$$h1(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$h1, _WRITE_READ_BENIGN_FLAG_$$h1;

implementation {:inline 1} _LOG_WRITE_$$h1(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$h1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$h1 == _value then true else _WRITE_HAS_OCCURRED_$$h1);
    _WRITE_READ_BENIGN_FLAG_$$h1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$h1 == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$h1);
    return;
}

procedure _CHECK_WRITE_$$h1(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$h1 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$h1 != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$h1 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$h1 != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$h1 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$h1(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$h1;

implementation {:inline 1} _LOG_ATOMIC_$$h1(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$h1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$h1);
    return;
}

procedure _CHECK_ATOMIC_$$h1(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$h1 && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$h1 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$h1(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$h1;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$h1(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$h1 := (if _P && _WRITE_HAS_OCCURRED_$$h1 && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$h1);
    return;
}

const _WATCHED_VALUE_$$h2: bv32;

procedure {:inline 1} _LOG_READ_$$h2(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$h2;

implementation {:inline 1} _LOG_READ_$$h2(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$h2 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$h2 == _value then true else _READ_HAS_OCCURRED_$$h2);
    return;
}

procedure _CHECK_READ_$$h2(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$h2 && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$h2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$h2 && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$h2: bool;

procedure {:inline 1} _LOG_WRITE_$$h2(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$h2, _WRITE_READ_BENIGN_FLAG_$$h2;

implementation {:inline 1} _LOG_WRITE_$$h2(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$h2 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$h2 == _value then true else _WRITE_HAS_OCCURRED_$$h2);
    _WRITE_READ_BENIGN_FLAG_$$h2 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$h2 == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$h2);
    return;
}

procedure _CHECK_WRITE_$$h2(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$h2 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$h2 != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$h2 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$h2 != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$h2 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$h2(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$h2;

implementation {:inline 1} _LOG_ATOMIC_$$h2(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$h2 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$h2);
    return;
}

procedure _CHECK_ATOMIC_$$h2(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$h2 && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$h2 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$h2(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$h2;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$h2(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$h2 := (if _P && _WRITE_HAS_OCCURRED_$$h2 && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$h2);
    return;
}

const _WATCHED_VALUE_$$foo.l: bv32;

procedure {:inline 1} _LOG_READ_$$foo.l(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$foo.l;

implementation {:inline 1} _LOG_READ_$$foo.l(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$foo.l := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.l == _value then true else _READ_HAS_OCCURRED_$$foo.l);
    return;
}

procedure _CHECK_READ_$$foo.l(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.l && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$foo.l && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.l && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$foo.l: bool;

procedure {:inline 1} _LOG_WRITE_$$foo.l(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$foo.l, _WRITE_READ_BENIGN_FLAG_$$foo.l;

implementation {:inline 1} _LOG_WRITE_$$foo.l(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$foo.l := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.l == _value then true else _WRITE_HAS_OCCURRED_$$foo.l);
    _WRITE_READ_BENIGN_FLAG_$$foo.l := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.l == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$foo.l);
    return;
}

procedure _CHECK_WRITE_$$foo.l(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.l && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.l != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.l && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.l != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.l && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$foo.l(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$foo.l;

implementation {:inline 1} _LOG_ATOMIC_$$foo.l(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$foo.l := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$foo.l);
    return;
}

procedure _CHECK_ATOMIC_$$foo.l(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.l && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.l && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.l(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$foo.l;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.l(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$foo.l := (if _P && _WRITE_HAS_OCCURRED_$$foo.l && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$foo.l);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
