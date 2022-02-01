//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "p"} {:global} $$p: [bv32]bv32;

axiom {:array_info "$$p"} {:global} {:elem_width 32} {:source_name "p"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$p: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$p: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$p: bool;

var {:source_name "q"} {:global} $$q: [bv32]bv32;

axiom {:array_info "$$q"} {:global} {:elem_width 32} {:source_name "q"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$q: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$q: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$q: bool;

const _WATCHED_OFFSET: bv32;

const {:global_offset_x} global_offset_x: bv32;

const {:global_offset_y} global_offset_y: bv32;

const {:global_offset_z} global_offset_z: bv32;

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

function FADD32(bv32, bv32) : bv32;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;

procedure {:source_name "foo"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$p && !_WRITE_HAS_OCCURRED_$$p && !_ATOMIC_HAS_OCCURRED_$$p;
  requires !_READ_HAS_OCCURRED_$$q && !_WRITE_HAS_OCCURRED_$$q && !_ATOMIC_HAS_OCCURRED_$$q;
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
  modifies $$p, $$q, _TRACKING, _READ_HAS_OCCURRED_$$q, _WRITE_HAS_OCCURRED_$$q, _WRITE_READ_BENIGN_FLAG_$$q, _WRITE_READ_BENIGN_FLAG_$$q, _READ_HAS_OCCURRED_$$p, _WRITE_HAS_OCCURRED_$$p, _WRITE_READ_BENIGN_FLAG_$$p, _WRITE_READ_BENIGN_FLAG_$$p;

implementation {:source_name "foo"} ULTIMATE.start()
{
  var $i.0: bv32;
  var $i3.0: bv32;
  var v0: bool;
  var v1$1: bv32;
  var v1$2: bv32;
  var v2: bool;
  var v3$1: bv32;
  var v3$2: bv32;

  $entry:
    $i.0 := 0bv32;
    assume {:captureState "loop_entry_state_1_0"} true;
    goto $for.cond;

  $for.cond:
    assume {:captureState "loop_head_state_1"} true;
    assert {:block_sourceloc} {:sourceloc_num 1} true;
    v0 := BV32_SLT($i.0, 100bv32);
    goto $truebb, __partitioned_block_$falsebb_0;

  __partitioned_block_$falsebb_0:
    assume {:partition} !v0;
    goto __partitioned_block_$falsebb_1;

  __partitioned_block_$falsebb_1:
    call $bugle_barrier_duplicated_0(0bv1, 1bv1);
    $i3.0 := 0bv32;
    assume {:captureState "loop_entry_state_0_0"} true;
    goto $for.cond4;

  $for.cond4:
    assume {:captureState "loop_head_state_0"} true;
    assert {:block_sourceloc} {:sourceloc_num 8} true;
    v2 := BV32_SLT($i3.0, 100bv32);
    goto $truebb0, $falsebb0;

  $falsebb0:
    assume {:partition} !v2;
    return;

  $truebb0:
    assume {:partition} v2;
    call _LOG_READ_$$q(true, BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), $$q[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 10} true;
    call _CHECK_READ_$$q(true, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), $$q[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$q"} true;
    v3$1 := $$q[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)];
    v3$2 := $$q[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)];
    call _LOG_WRITE_$$q(true, BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), FADD32(v3$1, 1065353216bv32), $$q[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$q(true, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 11} true;
    call _CHECK_WRITE_$$q(true, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), FADD32(v3$2, 1065353216bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$q"} true;
    $$q[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)] := FADD32(v3$1, 1065353216bv32);
    $$q[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)] := FADD32(v3$2, 1065353216bv32);
    $i3.0 := BV32_ADD($i3.0, 1bv32);
    assume {:captureState "loop_back_edge_state_0_0"} true;
    goto $for.cond4;

  $truebb:
    assume {:partition} v0;
    call _LOG_READ_$$p(true, BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), $$p[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 3} true;
    call _CHECK_READ_$$p(true, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), $$p[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$p"} true;
    v1$1 := $$p[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)];
    v1$2 := $$p[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)];
    call _LOG_WRITE_$$p(true, BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), FADD32(v1$1, 1065353216bv32), $$p[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$p(true, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 4} true;
    call _CHECK_WRITE_$$p(true, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), FADD32(v1$2, 1065353216bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$p"} true;
    $$p[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)] := FADD32(v1$1, 1065353216bv32);
    $$p[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)] := FADD32(v1$2, 1065353216bv32);
    $i.0 := BV32_ADD($i.0, 1bv32);
    assume {:captureState "loop_back_edge_state_1_0"} true;
    goto $for.cond;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 1024bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 1024bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_x == 0bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_y == 0bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_z == 0bv32 then 1bv1 else 0bv1) != 0bv1;

const {:local_id_y} local_id_y$1: bv32;

const {:local_id_y} local_id_y$2: bv32;

const {:local_id_z} local_id_z$1: bv32;

const {:local_id_z} local_id_z$2: bv32;

const {:group_id_y} group_id_y$1: bv32;

const {:group_id_y} group_id_y$2: bv32;

const {:group_id_z} group_id_z$1: bv32;

const {:group_id_z} group_id_z$2: bv32;

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_0($0: bv1, $1: bv1);
  requires $0 == 0bv1;
  requires $1 == 1bv1;
  modifies $$p, $$q, _TRACKING;

const _WATCHED_VALUE_$$p: bv32;

procedure {:inline 1} _LOG_READ_$$p(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$p;

implementation {:inline 1} _LOG_READ_$$p(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then true else _READ_HAS_OCCURRED_$$p);
    return;
}

procedure _CHECK_READ_$$p(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$p);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$p: bool;

procedure {:inline 1} _LOG_WRITE_$$p(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$p, _WRITE_READ_BENIGN_FLAG_$$p;

implementation {:inline 1} _LOG_WRITE_$$p(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then true else _WRITE_HAS_OCCURRED_$$p);
    _WRITE_READ_BENIGN_FLAG_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$p);
    return;
}

procedure _CHECK_WRITE_$$p(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$p(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$p;

implementation {:inline 1} _LOG_ATOMIC_$$p(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$p);
    return;
}

procedure _CHECK_ATOMIC_$$p(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$p;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$p := (if _P && _WRITE_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$p);
    return;
}

const _WATCHED_VALUE_$$q: bv32;

procedure {:inline 1} _LOG_READ_$$q(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$q;

implementation {:inline 1} _LOG_READ_$$q(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$q := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$q == _value then true else _READ_HAS_OCCURRED_$$q);
    return;
}

procedure _CHECK_READ_$$q(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$q);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$q: bool;

procedure {:inline 1} _LOG_WRITE_$$q(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$q, _WRITE_READ_BENIGN_FLAG_$$q;

implementation {:inline 1} _LOG_WRITE_$$q(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$q := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$q == _value then true else _WRITE_HAS_OCCURRED_$$q);
    _WRITE_READ_BENIGN_FLAG_$$q := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$q == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$q);
    return;
}

procedure _CHECK_WRITE_$$q(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$q != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$q != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$q(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$q;

implementation {:inline 1} _LOG_ATOMIC_$$q(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$q := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$q);
    return;
}

procedure _CHECK_ATOMIC_$$q(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$q(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$q;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$q(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$q := (if _P && _WRITE_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$q);
    return;
}

var _TRACKING: bool;

implementation {:inline 1} $bugle_barrier_duplicated_0($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$p;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$p;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$p;
    goto anon1;

  anon1:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$q;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$q;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$q;
    goto anon2;

  anon2:
    goto anon7_Then, anon7_Else;

  anon7_Else:
    assume {:partition} !(group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1));
    goto anon5;

  anon5:
    havoc _TRACKING;
    return;

  anon7_Then:
    assume {:partition} group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1);
    havoc $$p;
    goto anon4;

  anon4:
    havoc $$q;
    goto anon5;

  anon6_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;
