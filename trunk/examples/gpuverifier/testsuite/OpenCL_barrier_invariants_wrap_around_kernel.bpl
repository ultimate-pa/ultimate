//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "A"} {:group_shared} $$wrap_around.A: [bv1][bv32]bv32;

axiom {:array_info "$$wrap_around.A"} {:group_shared} {:elem_width 32} {:source_name "A"} {:source_elem_width 32} {:source_dimensions "8"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$wrap_around.A: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$wrap_around.A: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$wrap_around.A: bool;

var {:source_name "B"} {:group_shared} $$wrap_around.B: [bv1][bv32]bv32;

axiom {:array_info "$$wrap_around.B"} {:group_shared} {:elem_width 32} {:source_name "B"} {:source_elem_width 32} {:source_dimensions "8"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$wrap_around.B: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$wrap_around.B: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$wrap_around.B: bool;

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

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvurem"} BV32_UREM(bv32, bv32) : bv32;

procedure {:source_name "wrap_around"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$wrap_around.A && !_WRITE_HAS_OCCURRED_$$wrap_around.A && !_ATOMIC_HAS_OCCURRED_$$wrap_around.A;
  requires !_READ_HAS_OCCURRED_$$wrap_around.B && !_WRITE_HAS_OCCURRED_$$wrap_around.B && !_ATOMIC_HAS_OCCURRED_$$wrap_around.B;
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
  modifies $$wrap_around.A, $$wrap_around.B, _WRITE_HAS_OCCURRED_$$wrap_around.A, _WRITE_READ_BENIGN_FLAG_$$wrap_around.A, _WRITE_READ_BENIGN_FLAG_$$wrap_around.A, _NOT_ACCESSED_$$wrap_around.A, _NOT_ACCESSED_$$wrap_around.B, _TRACKING, _READ_HAS_OCCURRED_$$wrap_around.A, _WRITE_HAS_OCCURRED_$$wrap_around.B, _WRITE_READ_BENIGN_FLAG_$$wrap_around.B, _WRITE_READ_BENIGN_FLAG_$$wrap_around.B, _READ_HAS_OCCURRED_$$wrap_around.B;

implementation {:source_name "wrap_around"} ULTIMATE.start()
{
  var v0$1: bv32;
  var v0$2: bv32;
  var v1$1: bv32;
  var v1$2: bv32;

  __partitioned_block_$entry_0:
    call _LOG_WRITE_$$wrap_around.A(true, local_id_x$1, local_id_x$1, $$wrap_around.A[1bv1][local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$wrap_around.A(true, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 1} true;
    call _CHECK_WRITE_$$wrap_around.A(true, local_id_x$2, local_id_x$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$wrap_around.A"} true;
    $$wrap_around.A[1bv1][local_id_x$1] := local_id_x$1;
    $$wrap_around.A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] := local_id_x$2;
    assume _NOT_ACCESSED_$$wrap_around.A != local_id_x$1 && _NOT_ACCESSED_$$wrap_around.A != local_id_x$2;
    assert {:barrier_invariant true} {:sourceloc_num 2} {:thread 1} true ==> (if $$wrap_around.A[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assert {:barrier_invariant_access_check true} {:sourceloc_num 2} {:thread 1} true ==> true ==> _NOT_ACCESSED_$$wrap_around.A != local_id_x$1;
    goto __partitioned_block_$entry_1;

  __partitioned_block_$entry_1:
    call $bugle_barrier_duplicated_0(1bv1, 0bv1);
    assume true ==> BV32_SGE(local_id_x$1, 0bv32) && BV32_SLT(local_id_x$1, group_size_x) ==> (if $$wrap_around.A[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$2, 0bv32) && BV32_SLT(local_id_x$2, group_size_x) ==> (if $$wrap_around.A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] == local_id_x$2 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(BV32_UREM(BV32_ADD(local_id_x$1, 1bv32), 8bv32), 0bv32) && BV32_SLT(BV32_UREM(BV32_ADD(local_id_x$1, 1bv32), 8bv32), group_size_x) ==> (if $$wrap_around.A[1bv1][BV32_UREM(BV32_ADD(local_id_x$1, 1bv32), 8bv32)] == BV32_UREM(BV32_ADD(local_id_x$1, 1bv32), 8bv32) then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(BV32_UREM(BV32_ADD(local_id_x$2, 1bv32), 8bv32), 0bv32) && BV32_SLT(BV32_UREM(BV32_ADD(local_id_x$2, 1bv32), 8bv32), group_size_x) ==> (if $$wrap_around.A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_UREM(BV32_ADD(local_id_x$2, 1bv32), 8bv32)] == BV32_UREM(BV32_ADD(local_id_x$2, 1bv32), 8bv32) then 1bv1 else 0bv1) != 0bv1;
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 4} true;
    v0$1 := $$wrap_around.A[1bv1][BV32_UREM(BV32_ADD(local_id_x$1, 1bv32), 8bv32)];
    v0$2 := $$wrap_around.A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_UREM(BV32_ADD(local_id_x$2, 1bv32), 8bv32)];
    assume _NOT_ACCESSED_$$wrap_around.A != BV32_UREM(BV32_ADD(local_id_x$1, 1bv32), 8bv32) && _NOT_ACCESSED_$$wrap_around.A != BV32_UREM(BV32_ADD(local_id_x$2, 1bv32), 8bv32);
    call _LOG_WRITE_$$wrap_around.B(true, v0$1, local_id_x$1, $$wrap_around.B[1bv1][v0$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$wrap_around.B(true, v0$2);
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 5} true;
    call _CHECK_WRITE_$$wrap_around.B(true, v0$2, local_id_x$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$wrap_around.B"} true;
    $$wrap_around.B[1bv1][v0$1] := local_id_x$1;
    $$wrap_around.B[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v0$2] := local_id_x$2;
    assume _NOT_ACCESSED_$$wrap_around.B != v0$1 && _NOT_ACCESSED_$$wrap_around.B != v0$2;
    call _LOG_READ_$$wrap_around.B(true, BV32_UREM(BV32_ADD(local_id_x$1, 1bv32), 8bv32), $$wrap_around.B[1bv1][BV32_UREM(BV32_ADD(local_id_x$1, 1bv32), 8bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 6} true;
    call _CHECK_READ_$$wrap_around.B(true, BV32_UREM(BV32_ADD(local_id_x$2, 1bv32), 8bv32), $$wrap_around.B[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_UREM(BV32_ADD(local_id_x$2, 1bv32), 8bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$wrap_around.B"} true;
    v1$1 := $$wrap_around.B[1bv1][BV32_UREM(BV32_ADD(local_id_x$1, 1bv32), 8bv32)];
    v1$2 := $$wrap_around.B[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_UREM(BV32_ADD(local_id_x$2, 1bv32), 8bv32)];
    assume _NOT_ACCESSED_$$wrap_around.B != BV32_UREM(BV32_ADD(local_id_x$1, 1bv32), 8bv32) && _NOT_ACCESSED_$$wrap_around.B != BV32_UREM(BV32_ADD(local_id_x$2, 1bv32), 8bv32);
    assert {:sourceloc_num 7} {:thread 1} (if v1$1 == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 7} {:thread 2} (if v1$2 == local_id_x$2 then 1bv1 else 0bv1) != 0bv1;
    return;
}

procedure {:source_name "__barrier_invariant_2"} {:barrier_invariant} $__barrier_invariant_22($expr$1: bv1, $instantiation1$1: bv32, $instantiation2$1: bv32, $expr$2: bv1, $instantiation1$2: bv32, $instantiation2$2: bv32);

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 8bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 1bv32 then 1bv1 else 0bv1) != 0bv1;

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
  modifies $$wrap_around.A, $$wrap_around.B, _NOT_ACCESSED_$$wrap_around.A, _NOT_ACCESSED_$$wrap_around.B, _TRACKING;

var {:check_access} _NOT_ACCESSED_$$wrap_around.A: bv32;

var {:check_access} _NOT_ACCESSED_$$wrap_around.B: bv32;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;

const _WATCHED_VALUE_$$wrap_around.A: bv32;

procedure {:inline 1} _LOG_READ_$$wrap_around.A(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$wrap_around.A;

implementation {:inline 1} _LOG_READ_$$wrap_around.A(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$wrap_around.A := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$wrap_around.A == _value then true else _READ_HAS_OCCURRED_$$wrap_around.A);
    return;
}

procedure _CHECK_READ_$$wrap_around.A(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$wrap_around.A && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$wrap_around.A && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$wrap_around.A && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$wrap_around.A: bool;

procedure {:inline 1} _LOG_WRITE_$$wrap_around.A(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$wrap_around.A, _WRITE_READ_BENIGN_FLAG_$$wrap_around.A;

implementation {:inline 1} _LOG_WRITE_$$wrap_around.A(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$wrap_around.A := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$wrap_around.A == _value then true else _WRITE_HAS_OCCURRED_$$wrap_around.A);
    _WRITE_READ_BENIGN_FLAG_$$wrap_around.A := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$wrap_around.A == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$wrap_around.A);
    return;
}

procedure _CHECK_WRITE_$$wrap_around.A(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$wrap_around.A && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$wrap_around.A != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$wrap_around.A && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$wrap_around.A != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$wrap_around.A && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$wrap_around.A(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$wrap_around.A;

implementation {:inline 1} _LOG_ATOMIC_$$wrap_around.A(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$wrap_around.A := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$wrap_around.A);
    return;
}

procedure _CHECK_ATOMIC_$$wrap_around.A(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$wrap_around.A && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$wrap_around.A && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$wrap_around.A(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$wrap_around.A;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$wrap_around.A(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$wrap_around.A := (if _P && _WRITE_HAS_OCCURRED_$$wrap_around.A && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$wrap_around.A);
    return;
}

const _WATCHED_VALUE_$$wrap_around.B: bv32;

procedure {:inline 1} _LOG_READ_$$wrap_around.B(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$wrap_around.B;

implementation {:inline 1} _LOG_READ_$$wrap_around.B(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$wrap_around.B := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$wrap_around.B == _value then true else _READ_HAS_OCCURRED_$$wrap_around.B);
    return;
}

procedure _CHECK_READ_$$wrap_around.B(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$wrap_around.B && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$wrap_around.B && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$wrap_around.B && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$wrap_around.B: bool;

procedure {:inline 1} _LOG_WRITE_$$wrap_around.B(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$wrap_around.B, _WRITE_READ_BENIGN_FLAG_$$wrap_around.B;

implementation {:inline 1} _LOG_WRITE_$$wrap_around.B(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$wrap_around.B := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$wrap_around.B == _value then true else _WRITE_HAS_OCCURRED_$$wrap_around.B);
    _WRITE_READ_BENIGN_FLAG_$$wrap_around.B := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$wrap_around.B == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$wrap_around.B);
    return;
}

procedure _CHECK_WRITE_$$wrap_around.B(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$wrap_around.B && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$wrap_around.B != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$wrap_around.B && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$wrap_around.B != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$wrap_around.B && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$wrap_around.B(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$wrap_around.B;

implementation {:inline 1} _LOG_ATOMIC_$$wrap_around.B(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$wrap_around.B := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$wrap_around.B);
    return;
}

procedure _CHECK_ATOMIC_$$wrap_around.B(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$wrap_around.B && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$wrap_around.B && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$wrap_around.B(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$wrap_around.B;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$wrap_around.B(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$wrap_around.B := (if _P && _WRITE_HAS_OCCURRED_$$wrap_around.B && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$wrap_around.B);
    return;
}

var _TRACKING: bool;

implementation {:inline 1} $bugle_barrier_duplicated_0($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon8_Then, anon8_Else;

  anon8_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$wrap_around.A;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$wrap_around.A;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$wrap_around.A;
    goto anon1;

  anon1:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$wrap_around.B;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$wrap_around.B;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$wrap_around.B;
    goto anon2;

  anon2:
    goto anon9_Then, anon9_Else;

  anon9_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon7;

  anon7:
    havoc _TRACKING;
    return;

  anon9_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$wrap_around.A;
    goto anon4;

  anon4:
    havoc $$wrap_around.B;
    goto anon5;

  anon5:
    havoc _NOT_ACCESSED_$$wrap_around.A;
    goto anon6;

  anon6:
    havoc _NOT_ACCESSED_$$wrap_around.B;
    goto anon7;

  anon8_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;
