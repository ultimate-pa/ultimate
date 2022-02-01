//#Unsafe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "A"} {:group_shared} $$foo.A: [bv1][bv32]bv32;

axiom {:array_info "$$foo.A"} {:group_shared} {:elem_width 32} {:source_name "A"} {:source_elem_width 32} {:source_dimensions "128"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$foo.A: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$foo.A: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$foo.A: bool;

const _WATCHED_OFFSET: bv32;

const {:global_offset_x} global_offset_x: bv32;

const {:global_offset_y} global_offset_y: bv32;

const {:global_offset_z} global_offset_z: bv32;

const {:group_size_x} group_size_x: bv32;

const {:group_size_y} group_size_y: bv32;

const {:group_size_z} group_size_z: bv32;

const {:local_id_x} local_id_x$1: bv32;

const {:local_id_x} local_id_x$2: bv32;

const {:num_groups_x} num_groups_x: bv32;

const {:num_groups_y} num_groups_y: bv32;

const {:num_groups_z} num_groups_z: bv32;

function __other_bv32(bv32) : bv32;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvand"} BV32_AND(bv32, bv32) : bv32;

function {:builtin "zero_extend 31"} BV1_ZEXT32(bv1) : bv32;

procedure {:source_name "foo"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$foo.A && !_WRITE_HAS_OCCURRED_$$foo.A && !_ATOMIC_HAS_OCCURRED_$$foo.A;
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
  modifies $$foo.A, _WRITE_HAS_OCCURRED_$$foo.A, _WRITE_READ_BENIGN_FLAG_$$foo.A, _WRITE_READ_BENIGN_FLAG_$$foo.A, _NOT_ACCESSED_$$foo.A, _TRACKING, _TRACKING;

implementation {:source_name "foo"} ULTIMATE.start()
{

  __partitioned_block_$entry_0:
    call _LOG_WRITE_$$foo.A(true, local_id_x$1, local_id_x$1, $$foo.A[1bv1][local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.A(true, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 1} true;
    call _CHECK_WRITE_$$foo.A(true, local_id_x$2, local_id_x$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$foo.A"} true;
    $$foo.A[1bv1][local_id_x$1] := local_id_x$1;
    $$foo.A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] := local_id_x$2;
    assume _NOT_ACCESSED_$$foo.A != local_id_x$1 && _NOT_ACCESSED_$$foo.A != local_id_x$2;
    assert {:barrier_invariant true} {:sourceloc_num 2} {:thread 1} true ==> (if $$foo.A[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assert {:barrier_invariant_access_check true} {:sourceloc_num 2} {:thread 1} true ==> true ==> _NOT_ACCESSED_$$foo.A != local_id_x$1;
    goto __partitioned_block_$entry_1;

  __partitioned_block_$entry_1:
    call $bugle_barrier_duplicated_0(1bv1, 0bv1);
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.A[1bv1][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    call _LOG_WRITE_$$foo.A(true, local_id_x$1, BV32_ADD(local_id_x$1, 1bv32), $$foo.A[1bv1][local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.A(true, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 4} true;
    call _CHECK_WRITE_$$foo.A(true, local_id_x$2, BV32_ADD(local_id_x$2, 1bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$foo.A"} true;
    $$foo.A[1bv1][local_id_x$1] := BV32_ADD(local_id_x$1, 1bv32);
    $$foo.A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] := BV32_ADD(local_id_x$2, 1bv32);
    assume _NOT_ACCESSED_$$foo.A != local_id_x$1 && _NOT_ACCESSED_$$foo.A != local_id_x$2;
    assert {:barrier_invariant true} {:sourceloc_num 5} {:thread 1} group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> true ==> (if BV32_AND(BV1_ZEXT32((if local_id_x$1 != 0bv32 then 1bv1 else 0bv1)), BV1_ZEXT32((if local_id_x$2 != 0bv32 then 1bv1 else 0bv1))) != 0bv32 ==> $$foo.A[1bv1][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assert {:barrier_invariant_access_check true} {:sourceloc_num 5} {:thread 1} true ==> BV32_AND(BV1_ZEXT32((if local_id_x$1 != 0bv32 then 1bv1 else 0bv1)), BV1_ZEXT32((if local_id_x$2 != 0bv32 then 1bv1 else 0bv1))) != 0bv32 ==> _NOT_ACCESSED_$$foo.A != 0bv32;
    goto __partitioned_block_$entry_2;

  __partitioned_block_$entry_2:
    call $bugle_barrier_duplicated_1(1bv1, 0bv1);
    assume true ==> BV32_SGE(local_id_x$1, 0bv32) && BV32_SLT(local_id_x$1, group_size_x) && BV32_SGE(local_id_x$2, 0bv32) && BV32_SLT(local_id_x$2, group_size_x) && local_id_x$1 != local_id_x$2 ==> (if BV32_AND(BV1_ZEXT32((if local_id_x$1 != 0bv32 then 1bv1 else 0bv1)), BV1_ZEXT32((if local_id_x$2 != 0bv32 then 1bv1 else 0bv1))) != 0bv32 ==> $$foo.A[1bv1][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$2, 0bv32) && BV32_SLT(local_id_x$2, group_size_x) && BV32_SGE(local_id_x$1, 0bv32) && BV32_SLT(local_id_x$1, group_size_x) && local_id_x$2 != local_id_x$1 ==> (if BV32_AND(BV1_ZEXT32((if local_id_x$2 != 0bv32 then 1bv1 else 0bv1)), BV1_ZEXT32((if local_id_x$1 != 0bv32 then 1bv1 else 0bv1))) != 0bv32 ==> $$foo.A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    return;
}

procedure {:source_name "__barrier_invariant_1"} {:barrier_invariant} $__barrier_invariant_11($instantiation1: bv32, $expr$1: bv1, $expr$2: bv1);
  requires $instantiation1 == 0bv32;

procedure {:source_name "__barrier_invariant_binary_1"} {:binary_barrier_invariant} $__barrier_invariant_binary_11($expr$1: bv1, $instantiation0_1$1: bv32, $instantiation1_2$1: bv32, $expr$2: bv1, $instantiation0_1$2: bv32, $instantiation1_2$2: bv32);

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 128bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 64bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_x == 0bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_y == 0bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_z == 0bv32 then 1bv1 else 0bv1) != 0bv1;

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
  requires $1 == 0bv1;
  modifies $$foo.A, _NOT_ACCESSED_$$foo.A, _TRACKING;

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_1($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 0bv1;
  modifies $$foo.A, _NOT_ACCESSED_$$foo.A, _TRACKING;

var {:check_access} _NOT_ACCESSED_$$foo.A: bv32;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;

const _WATCHED_VALUE_$$foo.A: bv32;

procedure {:inline 1} _LOG_READ_$$foo.A(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$foo.A;

implementation {:inline 1} _LOG_READ_$$foo.A(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$foo.A := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.A == _value then true else _READ_HAS_OCCURRED_$$foo.A);
    return;
}

procedure _CHECK_READ_$$foo.A(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.A && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$foo.A && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.A && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$foo.A: bool;

procedure {:inline 1} _LOG_WRITE_$$foo.A(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$foo.A, _WRITE_READ_BENIGN_FLAG_$$foo.A;

implementation {:inline 1} _LOG_WRITE_$$foo.A(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$foo.A := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.A == _value then true else _WRITE_HAS_OCCURRED_$$foo.A);
    _WRITE_READ_BENIGN_FLAG_$$foo.A := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.A == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$foo.A);
    return;
}

procedure _CHECK_WRITE_$$foo.A(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.A && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.A != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.A && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.A != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.A && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$foo.A(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$foo.A;

implementation {:inline 1} _LOG_ATOMIC_$$foo.A(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$foo.A := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$foo.A);
    return;
}

procedure _CHECK_ATOMIC_$$foo.A(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.A && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.A && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.A(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$foo.A;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.A(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$foo.A := (if _P && _WRITE_HAS_OCCURRED_$$foo.A && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$foo.A);
    return;
}

var _TRACKING: bool;

implementation {:inline 1} $bugle_barrier_duplicated_0($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon5_Then, anon5_Else;

  anon5_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$foo.A;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$foo.A;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$foo.A;
    goto anon1;

  anon1:
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon4;

  anon4:
    havoc _TRACKING;
    return;

  anon6_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$foo.A;
    goto anon3;

  anon3:
    havoc _NOT_ACCESSED_$$foo.A;
    goto anon4;

  anon5_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

implementation {:inline 1} $bugle_barrier_duplicated_1($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon5_Then, anon5_Else;

  anon5_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$foo.A;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$foo.A;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$foo.A;
    goto anon1;

  anon1:
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon4;

  anon4:
    havoc _TRACKING;
    return;

  anon6_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$foo.A;
    goto anon3;

  anon3:
    havoc _NOT_ACCESSED_$$foo.A;
    goto anon4;

  anon5_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;
