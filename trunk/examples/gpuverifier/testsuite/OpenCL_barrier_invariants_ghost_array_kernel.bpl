//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

axiom {:array_info "$$__read_permission_temp"} {:elem_width 32} {:source_name "__read_permission_temp"} {:source_elem_width 32} {:source_dimensions "1"} true;

var {:source_name "A"} {:group_shared} $$foo.A: [bv1][bv32]bv32;

axiom {:array_info "$$foo.A"} {:group_shared} {:elem_width 32} {:source_name "A"} {:source_elem_width 32} {:source_dimensions "128"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$foo.A: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$foo.A: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$foo.A: bool;

var {:source_name "A_ghost"} {:group_shared} $$foo.A_ghost: [bv1][bv32]bv32;

axiom {:array_info "$$foo.A_ghost"} {:group_shared} {:elem_width 32} {:source_name "A_ghost"} {:source_elem_width 32} {:source_dimensions "128"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$foo.A_ghost: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$foo.A_ghost: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$foo.A_ghost: bool;

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

function {:builtin "bvsle"} BV32_SLE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;

procedure {:source_name "foo"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$foo.A && !_WRITE_HAS_OCCURRED_$$foo.A && !_ATOMIC_HAS_OCCURRED_$$foo.A;
  requires !_READ_HAS_OCCURRED_$$foo.A_ghost && !_WRITE_HAS_OCCURRED_$$foo.A_ghost && !_ATOMIC_HAS_OCCURRED_$$foo.A_ghost;
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
  modifies $$foo.A, _WRITE_HAS_OCCURRED_$$foo.A, _WRITE_READ_BENIGN_FLAG_$$foo.A, _WRITE_READ_BENIGN_FLAG_$$foo.A, _READ_HAS_OCCURRED_$$foo.A_ghost, $$foo.A_ghost, _NOT_ACCESSED_$$foo.A, _NOT_ACCESSED_$$foo.A_ghost, _TRACKING, _READ_HAS_OCCURRED_$$foo.A;

implementation {:source_name "foo"} ULTIMATE.start()
{
  var $i.0: bv32;
  var v0: bool;
  var v1$1: bv32;
  var v1$2: bv32;
  var v2$1: bv32;
  var v2$2: bv32;
  var v3$1: bv32;
  var v3$2: bv32;
  var v4$1: bv32;
  var v4$2: bv32;
  var v5$1: bv32;
  var v5$2: bv32;

  $entry:
    call _LOG_WRITE_$$foo.A(true, local_id_x$1, local_id_x$1, $$foo.A[1bv1][local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.A(true, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 1} true;
    call _CHECK_WRITE_$$foo.A(true, local_id_x$2, local_id_x$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$foo.A"} true;
    $$foo.A[1bv1][local_id_x$1] := local_id_x$1;
    $$foo.A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] := local_id_x$2;
    assume _NOT_ACCESSED_$$foo.A != local_id_x$1 && _NOT_ACCESSED_$$foo.A != local_id_x$2;
    $$foo.A_ghost := $$foo.A;
    $i.0 := 0bv32;
    assume {:captureState "loop_entry_state_0_0"} true;
    goto $for.cond;

  $for.cond:
    assume {:captureState "loop_head_state_0"} true;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _ATOMIC_HAS_OCCURRED_$$foo.A_ghost ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _WRITE_HAS_OCCURRED_$$foo.A_ghost ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _READ_HAS_OCCURRED_$$foo.A_ghost ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _ATOMIC_HAS_OCCURRED_$$foo.A ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _WRITE_HAS_OCCURRED_$$foo.A ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _READ_HAS_OCCURRED_$$foo.A ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:block_sourceloc} {:sourceloc_num 2} true;
    assert {:originated_from_invariant} {:sourceloc_num 3} {:thread 1} (if $$foo.A[1bv1][local_id_x$1] == BV32_ADD($$foo.A_ghost[1bv1][local_id_x$1], $i.0) then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 3} {:thread 2} (if $$foo.A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] == BV32_ADD($$foo.A_ghost[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2], $i.0) then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 4} {:thread 1} (if BV32_SLE($i.0, 10000bv32) then 1bv1 else 0bv1) != 0bv1;
    v0 := BV32_SLT($i.0, 10000bv32);
    goto $truebb, __partitioned_block_$falsebb_0;

  __partitioned_block_$falsebb_0:
    assume {:partition} !v0;
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 10} true;
    v3$1 := $$foo.A_ghost[1bv1][local_id_x$1];
    v3$2 := $$foo.A_ghost[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2];
    assume _NOT_ACCESSED_$$foo.A_ghost != local_id_x$1 && _NOT_ACCESSED_$$foo.A_ghost != local_id_x$2;
    $$__read_permission_temp$0bv32$1 := v3$1;
    $$__read_permission_temp$0bv32$2 := v3$2;
    assert {:barrier_invariant true} {:sourceloc_num 12} {:thread 1} true ==> (if $$foo.A[1bv1][local_id_x$1] == BV32_ADD($$foo.A_ghost[1bv1][local_id_x$1], 10000bv32) then 1bv1 else 0bv1) != 0bv1;
    assert {:barrier_invariant_access_check true} {:sourceloc_num 12} {:thread 1} true ==> true ==> _NOT_ACCESSED_$$foo.A != local_id_x$1;
    assert {:barrier_invariant_access_check true} {:sourceloc_num 12} {:thread 1} true ==> true ==> _NOT_ACCESSED_$$foo.A_ghost != local_id_x$1;
    goto __partitioned_block_$falsebb_1;

  __partitioned_block_$falsebb_1:
    call $bugle_barrier_duplicated_0(1bv1, 0bv1);
    assume true ==> BV32_SGE(local_id_x$1, 0bv32) && BV32_SLT(local_id_x$1, group_size_x) ==> (if $$foo.A[1bv1][local_id_x$1] == BV32_ADD($$foo.A_ghost[1bv1][local_id_x$1], 10000bv32) then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$2, 0bv32) && BV32_SLT(local_id_x$2, group_size_x) ==> (if $$foo.A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] == BV32_ADD($$foo.A_ghost[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2], 10000bv32) then 1bv1 else 0bv1) != 0bv1;
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 14} true;
    v4$1 := $$foo.A[1bv1][local_id_x$1];
    v4$2 := $$foo.A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2];
    assume _NOT_ACCESSED_$$foo.A != local_id_x$1 && _NOT_ACCESSED_$$foo.A != local_id_x$2;
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 15} true;
    v5$1 := $$foo.A_ghost[1bv1][local_id_x$1];
    v5$2 := $$foo.A_ghost[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2];
    assume _NOT_ACCESSED_$$foo.A_ghost != local_id_x$1 && _NOT_ACCESSED_$$foo.A_ghost != local_id_x$2;
    assert {:sourceloc_num 16} {:thread 1} (if v4$1 == BV32_ADD(v5$1, 10000bv32) then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 16} {:thread 2} (if v4$2 == BV32_ADD(v5$2, 10000bv32) then 1bv1 else 0bv1) != 0bv1;
    return;

  $truebb:
    assume {:partition} v0;
    v1$1 := local_id_x$1;
    v1$2 := local_id_x$2;
    call _LOG_READ_$$foo.A(true, v1$1, $$foo.A[1bv1][v1$1]);
    assume {:do_not_predicate} {:check_id "check_state_4"} {:captureState "check_state_4"} {:sourceloc} {:sourceloc_num 6} true;
    call _CHECK_READ_$$foo.A(true, v1$2, $$foo.A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$foo.A"} true;
    v2$1 := $$foo.A[1bv1][v1$1];
    v2$2 := $$foo.A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2];
    assume _NOT_ACCESSED_$$foo.A != v1$1 && _NOT_ACCESSED_$$foo.A != v1$2;
    call _LOG_WRITE_$$foo.A(true, v1$1, BV32_ADD(v2$1, 1bv32), $$foo.A[1bv1][v1$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.A(true, v1$2);
    assume {:do_not_predicate} {:check_id "check_state_5"} {:captureState "check_state_5"} {:sourceloc} {:sourceloc_num 7} true;
    call _CHECK_WRITE_$$foo.A(true, v1$2, BV32_ADD(v2$2, 1bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$foo.A"} true;
    $$foo.A[1bv1][v1$1] := BV32_ADD(v2$1, 1bv32);
    $$foo.A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2] := BV32_ADD(v2$2, 1bv32);
    assume _NOT_ACCESSED_$$foo.A != v1$1 && _NOT_ACCESSED_$$foo.A != v1$2;
    $i.0 := BV32_ADD($i.0, 1bv32);
    assume {:captureState "loop_back_edge_state_0_0"} true;
    goto $for.cond;
}

procedure {:source_name "__barrier_invariant_1"} {:barrier_invariant} $__barrier_invariant_11($expr$1: bv1, $instantiation1$1: bv32, $expr$2: bv1, $instantiation1$2: bv32);

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 64bv32 then 1bv1 else 0bv1) != 0bv1;

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
  modifies $$foo.A, $$foo.A_ghost, _NOT_ACCESSED_$$foo.A, _NOT_ACCESSED_$$foo.A_ghost, _TRACKING;

var $$__read_permission_temp$0bv32$1: bv32;

var $$__read_permission_temp$0bv32$2: bv32;

var {:check_access} _NOT_ACCESSED_$$foo.A: bv32;

var {:check_access} _NOT_ACCESSED_$$foo.A_ghost: bv32;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

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

const _WATCHED_VALUE_$$foo.A_ghost: bv32;

procedure {:inline 1} _LOG_READ_$$foo.A_ghost(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$foo.A_ghost;

implementation {:inline 1} _LOG_READ_$$foo.A_ghost(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$foo.A_ghost := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.A_ghost == _value then true else _READ_HAS_OCCURRED_$$foo.A_ghost);
    return;
}

procedure _CHECK_READ_$$foo.A_ghost(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.A_ghost && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$foo.A_ghost && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.A_ghost && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$foo.A_ghost: bool;

procedure {:inline 1} _LOG_WRITE_$$foo.A_ghost(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$foo.A_ghost, _WRITE_READ_BENIGN_FLAG_$$foo.A_ghost;

implementation {:inline 1} _LOG_WRITE_$$foo.A_ghost(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$foo.A_ghost := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.A_ghost == _value then true else _WRITE_HAS_OCCURRED_$$foo.A_ghost);
    _WRITE_READ_BENIGN_FLAG_$$foo.A_ghost := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.A_ghost == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$foo.A_ghost);
    return;
}

procedure _CHECK_WRITE_$$foo.A_ghost(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.A_ghost && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.A_ghost != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.A_ghost && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.A_ghost != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.A_ghost && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$foo.A_ghost(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$foo.A_ghost;

implementation {:inline 1} _LOG_ATOMIC_$$foo.A_ghost(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$foo.A_ghost := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$foo.A_ghost);
    return;
}

procedure _CHECK_ATOMIC_$$foo.A_ghost(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.A_ghost && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.A_ghost && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.A_ghost(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$foo.A_ghost;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.A_ghost(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$foo.A_ghost := (if _P && _WRITE_HAS_OCCURRED_$$foo.A_ghost && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$foo.A_ghost);
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
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$foo.A;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$foo.A;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$foo.A;
    goto anon1;

  anon1:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$foo.A_ghost;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$foo.A_ghost;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$foo.A_ghost;
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
    havoc $$foo.A;
    goto anon4;

  anon4:
    havoc $$foo.A_ghost;
    goto anon5;

  anon5:
    havoc _NOT_ACCESSED_$$foo.A;
    goto anon6;

  anon6:
    havoc _NOT_ACCESSED_$$foo.A_ghost;
    goto anon7;

  anon8_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;
