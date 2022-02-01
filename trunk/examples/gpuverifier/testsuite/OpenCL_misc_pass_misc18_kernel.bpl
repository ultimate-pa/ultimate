//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

axiom {:array_info "$$input"} {:global} {:elem_width 32} {:source_name "input"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$input: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$input: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$input: bool;

var {:source_name "output"} {:global} $$output: [bv32]bv32;

axiom {:array_info "$$output"} {:global} {:elem_width 32} {:source_name "output"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$output: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$output: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$output: bool;

var {:source_name "groupResults"} {:group_shared} $$reduction.groupResults: [bv1][bv32]bv32;

axiom {:array_info "$$reduction.groupResults"} {:group_shared} {:elem_width 32} {:source_name "groupResults"} {:source_elem_width 32} {:source_dimensions "64"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$reduction.groupResults: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$reduction.groupResults: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$reduction.groupResults: bool;

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

function UI32_TO_FP32(bv32) : bv32;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

procedure {:source_name "reduction"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$input && !_WRITE_HAS_OCCURRED_$$input && !_ATOMIC_HAS_OCCURRED_$$input;
  requires !_READ_HAS_OCCURRED_$$output && !_WRITE_HAS_OCCURRED_$$output && !_ATOMIC_HAS_OCCURRED_$$output;
  requires !_READ_HAS_OCCURRED_$$reduction.groupResults && !_WRITE_HAS_OCCURRED_$$reduction.groupResults && !_ATOMIC_HAS_OCCURRED_$$reduction.groupResults;
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
  modifies $$reduction.groupResults, _WRITE_HAS_OCCURRED_$$reduction.groupResults, _WRITE_READ_BENIGN_FLAG_$$reduction.groupResults, _WRITE_READ_BENIGN_FLAG_$$reduction.groupResults, _WRITE_HAS_OCCURRED_$$output, _WRITE_READ_BENIGN_FLAG_$$output, _WRITE_READ_BENIGN_FLAG_$$output, _NOT_ACCESSED_$$reduction.groupResults, $$output, _NOT_ACCESSED_$$output, _TRACKING;

implementation {:source_name "reduction"} ULTIMATE.start()
{
  var v0$1: bv32;
  var v0$2: bv32;

  __partitioned_block_$entry_0:
    havoc v0$1, v0$2;
    assume _NOT_ACCESSED_$$input != local_id_x$1 && _NOT_ACCESSED_$$input != local_id_x$2;
    call _LOG_WRITE_$$reduction.groupResults(true, local_id_x$1, UI32_TO_FP32(v0$1), $$reduction.groupResults[1bv1][local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$reduction.groupResults(true, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 2} true;
    call _CHECK_WRITE_$$reduction.groupResults(true, local_id_x$2, UI32_TO_FP32(v0$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$reduction.groupResults"} true;
    $$reduction.groupResults[1bv1][local_id_x$1] := UI32_TO_FP32(v0$1);
    $$reduction.groupResults[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] := UI32_TO_FP32(v0$2);
    assume _NOT_ACCESSED_$$reduction.groupResults != local_id_x$1 && _NOT_ACCESSED_$$reduction.groupResults != local_id_x$2;
    call _LOG_WRITE_$$output(true, BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 0bv32, $$output[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$output(true, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 3} true;
    call _CHECK_WRITE_$$output(true, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$output"} true;
    $$output[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)] := 0bv32;
    $$output[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)] := 0bv32;
    assume _NOT_ACCESSED_$$output != BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1) && _NOT_ACCESSED_$$output != BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2);
    assert {:barrier_invariant true} {:sourceloc_num 4} {:thread 1} true ==> (if $$output[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assert {:barrier_invariant_access_check true} {:sourceloc_num 4} {:thread 1} true ==> true ==> _NOT_ACCESSED_$$output != BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1);
    goto __partitioned_block_$entry_1;

  __partitioned_block_$entry_1:
    call $bugle_barrier_duplicated_0(1bv1, 0bv1);
    assume true ==> BV32_SGE(local_id_x$1, 0bv32) && BV32_SLT(local_id_x$1, group_size_x) ==> (if $$output[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$2, 0bv32) && BV32_SLT(local_id_x$2, group_size_x) ==> (if $$output[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    return;
}

procedure {:source_name "__barrier_invariant_1"} {:barrier_invariant} $__barrier_invariant_11($expr$1: bv1, $instantiation1$1: bv32, $expr$2: bv1, $instantiation1$2: bv32);

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 2bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 2bv32 then 1bv1 else 0bv1) != 0bv1;

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
  requires $0 == 1bv1;
  requires $1 == 0bv1;
  modifies $$reduction.groupResults, _NOT_ACCESSED_$$reduction.groupResults, $$output, _NOT_ACCESSED_$$output, _TRACKING;

var {:check_access} _NOT_ACCESSED_$$input: bv32;

var {:check_access} _NOT_ACCESSED_$$reduction.groupResults: bv32;

var {:check_access} _NOT_ACCESSED_$$output: bv32;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;

const _WATCHED_VALUE_$$input: bv32;

procedure {:inline 1} _LOG_READ_$$input(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$input;

implementation {:inline 1} _LOG_READ_$$input(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$input := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$input == _value then true else _READ_HAS_OCCURRED_$$input);
    return;
}

procedure _CHECK_READ_$$input(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$input && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$input);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$input && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$input: bool;

procedure {:inline 1} _LOG_WRITE_$$input(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$input, _WRITE_READ_BENIGN_FLAG_$$input;

implementation {:inline 1} _LOG_WRITE_$$input(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$input := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$input == _value then true else _WRITE_HAS_OCCURRED_$$input);
    _WRITE_READ_BENIGN_FLAG_$$input := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$input == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$input);
    return;
}

procedure _CHECK_WRITE_$$input(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$input && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$input != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$input && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$input != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$input && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$input(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$input;

implementation {:inline 1} _LOG_ATOMIC_$$input(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$input := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$input);
    return;
}

procedure _CHECK_ATOMIC_$$input(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$input && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$input && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$input(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$input;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$input(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$input := (if _P && _WRITE_HAS_OCCURRED_$$input && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$input);
    return;
}

const _WATCHED_VALUE_$$output: bv32;

procedure {:inline 1} _LOG_READ_$$output(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$output;

implementation {:inline 1} _LOG_READ_$$output(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$output := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$output == _value then true else _READ_HAS_OCCURRED_$$output);
    return;
}

procedure _CHECK_READ_$$output(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$output && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$output);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$output && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$output: bool;

procedure {:inline 1} _LOG_WRITE_$$output(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$output, _WRITE_READ_BENIGN_FLAG_$$output;

implementation {:inline 1} _LOG_WRITE_$$output(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$output := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$output == _value then true else _WRITE_HAS_OCCURRED_$$output);
    _WRITE_READ_BENIGN_FLAG_$$output := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$output == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$output);
    return;
}

procedure _CHECK_WRITE_$$output(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$output && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$output != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$output && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$output != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$output && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$output(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$output;

implementation {:inline 1} _LOG_ATOMIC_$$output(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$output := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$output);
    return;
}

procedure _CHECK_ATOMIC_$$output(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$output && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$output && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$output(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$output;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$output(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$output := (if _P && _WRITE_HAS_OCCURRED_$$output && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$output);
    return;
}

const _WATCHED_VALUE_$$reduction.groupResults: bv32;

procedure {:inline 1} _LOG_READ_$$reduction.groupResults(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$reduction.groupResults;

implementation {:inline 1} _LOG_READ_$$reduction.groupResults(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$reduction.groupResults := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$reduction.groupResults == _value then true else _READ_HAS_OCCURRED_$$reduction.groupResults);
    return;
}

procedure _CHECK_READ_$$reduction.groupResults(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$reduction.groupResults && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$reduction.groupResults && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$reduction.groupResults && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$reduction.groupResults: bool;

procedure {:inline 1} _LOG_WRITE_$$reduction.groupResults(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$reduction.groupResults, _WRITE_READ_BENIGN_FLAG_$$reduction.groupResults;

implementation {:inline 1} _LOG_WRITE_$$reduction.groupResults(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$reduction.groupResults := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$reduction.groupResults == _value then true else _WRITE_HAS_OCCURRED_$$reduction.groupResults);
    _WRITE_READ_BENIGN_FLAG_$$reduction.groupResults := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$reduction.groupResults == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$reduction.groupResults);
    return;
}

procedure _CHECK_WRITE_$$reduction.groupResults(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$reduction.groupResults && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$reduction.groupResults != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$reduction.groupResults && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$reduction.groupResults != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$reduction.groupResults && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$reduction.groupResults(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$reduction.groupResults;

implementation {:inline 1} _LOG_ATOMIC_$$reduction.groupResults(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$reduction.groupResults := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$reduction.groupResults);
    return;
}

procedure _CHECK_ATOMIC_$$reduction.groupResults(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$reduction.groupResults && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$reduction.groupResults && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$reduction.groupResults(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$reduction.groupResults;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$reduction.groupResults(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$reduction.groupResults := (if _P && _WRITE_HAS_OCCURRED_$$reduction.groupResults && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$reduction.groupResults);
    return;
}

var _TRACKING: bool;

implementation {:inline 1} $bugle_barrier_duplicated_0($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon9_Then, anon9_Else;

  anon9_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$reduction.groupResults;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$reduction.groupResults;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$reduction.groupResults;
    goto anon1;

  anon1:
    goto anon10_Then, anon10_Else;

  anon10_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon4;

  anon4:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$output;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$output;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$output;
    goto anon5;

  anon5:
    goto anon11_Then, anon11_Else;

  anon11_Else:
    assume {:partition} !(group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1));
    goto anon8;

  anon8:
    havoc _TRACKING;
    return;

  anon11_Then:
    assume {:partition} group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1);
    havoc $$output;
    goto anon7;

  anon7:
    havoc _NOT_ACCESSED_$$output;
    goto anon8;

  anon10_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$reduction.groupResults;
    goto anon3;

  anon3:
    havoc _NOT_ACCESSED_$$reduction.groupResults;
    goto anon4;

  anon9_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;
