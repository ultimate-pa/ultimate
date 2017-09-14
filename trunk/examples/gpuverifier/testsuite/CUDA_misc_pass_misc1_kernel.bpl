//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "S"} {:group_shared} $$_ZZ9helloCUDAiE1S: [bv1][bv32]bv32;

axiom {:array_info "$$_ZZ9helloCUDAiE1S"} {:group_shared} {:elem_width 32} {:source_name "S"} {:source_elem_width 32} {:source_dimensions "8192"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S: bool;

axiom {:array_info "$$_ZZ9helloCUDAiE1F"} {:group_shared} {:elem_width 32} {:source_name "F"} {:source_elem_width 32} {:source_dimensions "256"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F: bool;

const _WATCHED_OFFSET: bv32;

const {:group_size_x} group_size_x: bv32;

const {:group_size_y} group_size_y: bv32;

const {:group_size_z} group_size_z: bv32;

const {:local_id_x} local_id_x$1: bv32;

const {:local_id_x} local_id_x$2: bv32;

const {:num_groups_x} num_groups_x: bv32;

const {:num_groups_y} num_groups_y: bv32;

const {:num_groups_z} num_groups_z: bv32;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;

function {:builtin "bvudiv"} BV32_UDIV(bv32, bv32) : bv32;

function {:builtin "bvult"} BV32_ULT(bv32, bv32) : bool;

function {:builtin "bvurem"} BV32_UREM(bv32, bv32) : bv32;

procedure {:source_name "helloCUDA"} ULTIMATE.start($x: bv32);
  requires (if $x == 143bv32 then 1bv1 else 0bv1) != 0bv1;
  requires !_READ_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S && !_WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S && !_ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S;
  requires !_READ_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F && !_WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F && !_ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F;
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
  modifies $$_ZZ9helloCUDAiE1S, _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S, _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1S, _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1S;

implementation {:source_name "helloCUDA"} ULTIMATE.start($x: bv32)
{
  var $i.0: bv32;
  var v0: bool;
  var v1$1: bool;
  var v1$2: bool;
  var v2$1: bv32;
  var v2$2: bv32;
  var p0$1: bool;
  var p0$2: bool;
  var p1$1: bool;
  var p1$2: bool;
  var _HAVOC_bv32$1: bv32;
  var _HAVOC_bv32$2: bv32;

  $entry:
    $i.0 := 0bv32;
    assume {:captureState "loop_entry_state_0_0"} true;
    goto $for.cond;

  $for.cond:
    assume {:captureState "loop_head_state_0"} true;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:block_sourceloc} {:sourceloc_num 2} true;
    assert {:originated_from_invariant} {:sourceloc_num 3} {:thread 1} (if _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S ==> BV32_UREM(BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32), group_size_x) == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    v0 := BV32_SLT($i.0, $x);
    p0$1 := false;
    p0$2 := false;
    p1$1 := false;
    p1$2 := false;
    goto $truebb, $falsebb;

  $falsebb:
    assume {:partition} !v0;
    return;

  $truebb:
    assume {:partition} v0;
    v1$1 := BV32_ULT(BV32_ADD($i.0, BV32_UDIV(local_id_x$1, 32bv32)), $x);
    v1$2 := BV32_ULT(BV32_ADD($i.0, BV32_UDIV(local_id_x$2, 32bv32)), $x);
    p1$1 := (if v1$1 then v1$1 else p1$1);
    p1$2 := (if v1$2 then v1$2 else p1$2);
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    v2$1 := (if p1$1 then _HAVOC_bv32$1 else v2$1);
    v2$2 := (if p1$2 then _HAVOC_bv32$2 else v2$2);
    call _LOG_WRITE_$$_ZZ9helloCUDAiE1S(p1$1, BV32_ADD(BV32_MUL(BV32_ADD($i.0, BV32_UDIV(local_id_x$1, 32bv32)), 32bv32), BV32_UREM(local_id_x$1, 32bv32)), v2$1, $$_ZZ9helloCUDAiE1S[1bv1][BV32_ADD(BV32_MUL(BV32_ADD($i.0, BV32_UDIV(local_id_x$1, 32bv32)), 32bv32), BV32_UREM(local_id_x$1, 32bv32))]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1S(p1$2, BV32_ADD(BV32_MUL(BV32_ADD($i.0, BV32_UDIV(local_id_x$2, 32bv32)), 32bv32), BV32_UREM(local_id_x$2, 32bv32)));
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 7} true;
    call _CHECK_WRITE_$$_ZZ9helloCUDAiE1S(p1$2, BV32_ADD(BV32_MUL(BV32_ADD($i.0, BV32_UDIV(local_id_x$2, 32bv32)), 32bv32), BV32_UREM(local_id_x$2, 32bv32)), v2$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$_ZZ9helloCUDAiE1S"} true;
    $$_ZZ9helloCUDAiE1S[1bv1][BV32_ADD(BV32_MUL(BV32_ADD($i.0, BV32_UDIV(local_id_x$1, 32bv32)), 32bv32), BV32_UREM(local_id_x$1, 32bv32))] := (if p1$1 then v2$1 else $$_ZZ9helloCUDAiE1S[1bv1][BV32_ADD(BV32_MUL(BV32_ADD($i.0, BV32_UDIV(local_id_x$1, 32bv32)), 32bv32), BV32_UREM(local_id_x$1, 32bv32))]);
    $$_ZZ9helloCUDAiE1S[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(BV32_ADD($i.0, BV32_UDIV(local_id_x$2, 32bv32)), 32bv32), BV32_UREM(local_id_x$2, 32bv32))] := (if p1$2 then v2$2 else $$_ZZ9helloCUDAiE1S[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(BV32_ADD($i.0, BV32_UDIV(local_id_x$2, 32bv32)), 32bv32), BV32_UREM(local_id_x$2, 32bv32))]);
    $i.0 := BV32_ADD($i.0, BV32_UDIV(group_size_x, 32bv32));
    assume {:captureState "loop_back_edge_state_0_0"} true;
    goto $for.cond;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 512bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 1bv32 then 1bv1 else 0bv1) != 0bv1;

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

const _WATCHED_VALUE_$$_ZZ9helloCUDAiE1S: bv32;

procedure {:inline 1} _LOG_READ_$$_ZZ9helloCUDAiE1S(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S;

implementation {:inline 1} _LOG_READ_$$_ZZ9helloCUDAiE1S(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ9helloCUDAiE1S == _value then true else _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S);
    return;
}

procedure _CHECK_READ_$$_ZZ9helloCUDAiE1S(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1S && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1S: bool;

procedure {:inline 1} _LOG_WRITE_$$_ZZ9helloCUDAiE1S(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S, _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1S;

implementation {:inline 1} _LOG_WRITE_$$_ZZ9helloCUDAiE1S(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ9helloCUDAiE1S == _value then true else _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S);
    _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1S := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ9helloCUDAiE1S == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1S);
    return;
}

procedure _CHECK_WRITE_$$_ZZ9helloCUDAiE1S(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ9helloCUDAiE1S != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ9helloCUDAiE1S != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$_ZZ9helloCUDAiE1S(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S;

implementation {:inline 1} _LOG_ATOMIC_$$_ZZ9helloCUDAiE1S(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S);
    return;
}

procedure _CHECK_ATOMIC_$$_ZZ9helloCUDAiE1S(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1S(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1S;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1S(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1S := (if _P && _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1S && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1S);
    return;
}

const _WATCHED_VALUE_$$_ZZ9helloCUDAiE1F: bv32;

procedure {:inline 1} _LOG_READ_$$_ZZ9helloCUDAiE1F(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F;

implementation {:inline 1} _LOG_READ_$$_ZZ9helloCUDAiE1F(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ9helloCUDAiE1F == _value then true else _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F);
    return;
}

procedure _CHECK_READ_$$_ZZ9helloCUDAiE1F(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1F && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1F: bool;

procedure {:inline 1} _LOG_WRITE_$$_ZZ9helloCUDAiE1F(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F, _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1F;

implementation {:inline 1} _LOG_WRITE_$$_ZZ9helloCUDAiE1F(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ9helloCUDAiE1F == _value then true else _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F);
    _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1F := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ9helloCUDAiE1F == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1F);
    return;
}

procedure _CHECK_WRITE_$$_ZZ9helloCUDAiE1F(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ9helloCUDAiE1F != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ9helloCUDAiE1F != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$_ZZ9helloCUDAiE1F(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F;

implementation {:inline 1} _LOG_ATOMIC_$$_ZZ9helloCUDAiE1F(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F);
    return;
}

procedure _CHECK_ATOMIC_$$_ZZ9helloCUDAiE1F(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1F(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1F;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1F(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1F := (if _P && _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiE1F && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiE1F);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;
