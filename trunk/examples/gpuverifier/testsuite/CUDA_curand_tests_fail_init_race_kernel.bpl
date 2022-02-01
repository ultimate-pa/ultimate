//#Unsafe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "state"} {:global} $$state: [bv32]bv32;

axiom {:array_info "$$state"} {:global} {:elem_width 32} {:source_name "state"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$state: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$state: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$state: bool;

var {:source_name "A"} {:global} $$A: [bv32]bv32;

axiom {:array_info "$$A"} {:global} {:elem_width 32} {:source_name "A"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$A: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$A: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$A: bool;

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

procedure {:source_name "init_test"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$state && !_WRITE_HAS_OCCURRED_$$state && !_ATOMIC_HAS_OCCURRED_$$state;
  requires !_READ_HAS_OCCURRED_$$A && !_WRITE_HAS_OCCURRED_$$A && !_ATOMIC_HAS_OCCURRED_$$A;
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
  modifies _WRITE_HAS_OCCURRED_$$state, _WRITE_READ_BENIGN_FLAG_$$state, _WRITE_READ_BENIGN_FLAG_$$state, $$state, $$A, _TRACKING, _READ_HAS_OCCURRED_$$state, _WRITE_HAS_OCCURRED_$$A, _WRITE_READ_BENIGN_FLAG_$$A, _WRITE_READ_BENIGN_FLAG_$$A;

implementation {:source_name "init_test"} ULTIMATE.start()
{
  var v0$1: bv32;
  var v0$2: bv32;
  var v1$1: bool;
  var v1$2: bool;
  var v2$1: bv32;
  var v2$2: bv32;
  var v3$1: bv32;
  var v3$2: bv32;
  var v4$1: bv32;
  var v4$2: bv32;
  var p0$1: bool;
  var p0$2: bool;
  var p1$1: bool;
  var p1$2: bool;

  __partitioned_block_$entry_0:
    call v0$1, v0$2 := $_Z19__bugle_random_uintv(true, true);
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z19__bugle_random_uintv"} true;
    call _LOG_WRITE_$$state(true, 0bv32, v0$1, $$state[0bv32]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$state(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 2} true;
    call _CHECK_WRITE_$$state(true, 0bv32, v0$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$state"} true;
    $$state[0bv32] := v0$1;
    $$state[0bv32] := v0$2;
    goto __partitioned_block_$entry_1;

  __partitioned_block_$entry_1:
    call $bugle_barrier_duplicated_0(1bv1, 1bv1);
    v1$1 := local_id_x$1 == 0bv32;
    v1$2 := local_id_x$2 == 0bv32;
    p0$1 := false;
    p0$2 := false;
    p1$1 := false;
    p1$2 := false;
    p0$1 := (if v1$1 then v1$1 else p0$1);
    p0$2 := (if v1$2 then v1$2 else p0$2);
    call v2$1, v2$2 := $_Z19__bugle_random_uintv(p0$1, p0$2);
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z19__bugle_random_uintv"} true;
    call _LOG_READ_$$state(p0$1, 0bv32, $$state[0bv32]);
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 6} true;
    call _CHECK_READ_$$state(p0$2, 0bv32, $$state[0bv32]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$state"} true;
    v3$1 := (if p0$1 then $$state[0bv32] else v3$1);
    v3$2 := (if p0$2 then $$state[0bv32] else v3$2);
    call _LOG_WRITE_$$state(p0$1, 0bv32, BV32_ADD(v3$1, v2$1), $$state[0bv32]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$state(p0$2, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 7} true;
    call _CHECK_WRITE_$$state(p0$2, 0bv32, BV32_ADD(v3$2, v2$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$state"} true;
    $$state[0bv32] := (if p0$1 then BV32_ADD(v3$1, v2$1) else $$state[0bv32]);
    $$state[0bv32] := (if p0$2 then BV32_ADD(v3$2, v2$2) else $$state[0bv32]);
    call v4$1, v4$2 := $_Z19__bugle_random_uintv(p0$1, p0$2);
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z19__bugle_random_uintv"} true;
    call _LOG_WRITE_$$A(p0$1, 0bv32, v4$1, $$A[0bv32]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(p0$2, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 9} true;
    call _CHECK_WRITE_$$A(p0$2, 0bv32, v4$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A"} true;
    $$A[0bv32] := (if p0$1 then v4$1 else $$A[0bv32]);
    $$A[0bv32] := (if p0$2 then v4$2 else $$A[0bv32]);
    return;
}

procedure {:source_name "_Z19__bugle_random_uintv"} $_Z19__bugle_random_uintv(_P$1: bool, _P$2: bool) returns ($ret$1: bv32, $ret$2: bv32);

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 2bv32 then 1bv1 else 0bv1) != 0bv1;

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

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_0($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 1bv1;
  modifies $$state, $$A, _TRACKING;

const _WATCHED_VALUE_$$state: bv32;

procedure {:inline 1} _LOG_READ_$$state(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$state;

implementation {:inline 1} _LOG_READ_$$state(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$state := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$state == _value then true else _READ_HAS_OCCURRED_$$state);
    return;
}

procedure _CHECK_READ_$$state(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$state && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$state);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$state && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$state: bool;

procedure {:inline 1} _LOG_WRITE_$$state(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$state, _WRITE_READ_BENIGN_FLAG_$$state;

implementation {:inline 1} _LOG_WRITE_$$state(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$state := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$state == _value then true else _WRITE_HAS_OCCURRED_$$state);
    _WRITE_READ_BENIGN_FLAG_$$state := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$state == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$state);
    return;
}

procedure _CHECK_WRITE_$$state(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$state && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$state != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$state && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$state != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$state && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$state(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$state;

implementation {:inline 1} _LOG_ATOMIC_$$state(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$state := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$state);
    return;
}

procedure _CHECK_ATOMIC_$$state(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$state && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$state && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$state(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$state;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$state(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$state := (if _P && _WRITE_HAS_OCCURRED_$$state && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$state);
    return;
}

const _WATCHED_VALUE_$$A: bv32;

procedure {:inline 1} _LOG_READ_$$A(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$A;

implementation {:inline 1} _LOG_READ_$$A(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$A := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A == _value then true else _READ_HAS_OCCURRED_$$A);
    return;
}

procedure _CHECK_READ_$$A(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$A);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$A: bool;

procedure {:inline 1} _LOG_WRITE_$$A(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$A, _WRITE_READ_BENIGN_FLAG_$$A;

implementation {:inline 1} _LOG_WRITE_$$A(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$A := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A == _value then true else _WRITE_HAS_OCCURRED_$$A);
    _WRITE_READ_BENIGN_FLAG_$$A := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$A);
    return;
}

procedure _CHECK_WRITE_$$A(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$A(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$A;

implementation {:inline 1} _LOG_ATOMIC_$$A(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$A := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$A);
    return;
}

procedure _CHECK_ATOMIC_$$A(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$A;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$A := (if _P && _WRITE_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$A);
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
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$state;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$state;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$state;
    goto anon1;

  anon1:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$A;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$A;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$A;
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
    havoc $$state;
    goto anon4;

  anon4:
    havoc $$A;
    goto anon5;

  anon6_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
