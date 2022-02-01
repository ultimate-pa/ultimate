//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

axiom {:array_info "$$input"} {:global} {:elem_width 32} {:source_name "input"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$input: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$input: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$input: bool;

axiom {:array_info "$$output"} {:global} {:elem_width 32} {:source_name "output"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$output: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$output: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$output: bool;

var {:source_name "sum"} {:group_shared} $$k.sum: [bv1][bv32]bv32;

axiom {:array_info "$$k.sum"} {:group_shared} {:elem_width 32} {:source_name "sum"} {:source_elem_width 32} {:source_dimensions "1024"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$k.sum: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$k.sum: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$k.sum: bool;

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

function {:builtin "bvuge"} BV32_UGE(bv32, bv32) : bool;

procedure {:source_name "k"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$input && !_WRITE_HAS_OCCURRED_$$input && !_ATOMIC_HAS_OCCURRED_$$input;
  requires !_READ_HAS_OCCURRED_$$output && !_WRITE_HAS_OCCURRED_$$output && !_ATOMIC_HAS_OCCURRED_$$output;
  requires !_READ_HAS_OCCURRED_$$k.sum && !_WRITE_HAS_OCCURRED_$$k.sum && !_ATOMIC_HAS_OCCURRED_$$k.sum;
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
  modifies $$k.sum, _WRITE_HAS_OCCURRED_$$k.sum, _WRITE_READ_BENIGN_FLAG_$$k.sum, _WRITE_READ_BENIGN_FLAG_$$k.sum;

implementation {:source_name "k"} ULTIMATE.start()
{
  var v0$1: bool;
  var v0$2: bool;
  var v1$1: bv32;
  var v1$2: bv32;
  var p0$1: bool;
  var p0$2: bool;
  var p1$1: bool;
  var p1$2: bool;
  var _HAVOC_bv32$1: bv32;
  var _HAVOC_bv32$2: bv32;

  $entry:
    v0$1 := BV32_UGE(local_id_x$1, 1bv32);
    v0$2 := BV32_UGE(local_id_x$2, 1bv32);
    p0$1 := false;
    p0$2 := false;
    p1$1 := false;
    p1$2 := false;
    p0$1 := (if v0$1 then v0$1 else p0$1);
    p0$2 := (if v0$2 then v0$2 else p0$2);
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    v1$1 := (if p0$1 then _HAVOC_bv32$1 else v1$1);
    v1$2 := (if p0$2 then _HAVOC_bv32$2 else v1$2);
    call _LOG_WRITE_$$k.sum(p0$1, local_id_x$1, v1$1, $$k.sum[1bv1][local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$k.sum(p0$2, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 2} true;
    call _CHECK_WRITE_$$k.sum(p0$2, local_id_x$2, v1$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$k.sum"} true;
    $$k.sum[1bv1][local_id_x$1] := (if p0$1 then v1$1 else $$k.sum[1bv1][local_id_x$1]);
    $$k.sum[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] := (if p0$2 then v1$2 else $$k.sum[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2]);
    return;
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

const _WATCHED_VALUE_$$k.sum: bv32;

procedure {:inline 1} _LOG_READ_$$k.sum(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$k.sum;

implementation {:inline 1} _LOG_READ_$$k.sum(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$k.sum := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$k.sum == _value then true else _READ_HAS_OCCURRED_$$k.sum);
    return;
}

procedure _CHECK_READ_$$k.sum(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$k.sum && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$k.sum && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$k.sum && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$k.sum: bool;

procedure {:inline 1} _LOG_WRITE_$$k.sum(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$k.sum, _WRITE_READ_BENIGN_FLAG_$$k.sum;

implementation {:inline 1} _LOG_WRITE_$$k.sum(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$k.sum := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$k.sum == _value then true else _WRITE_HAS_OCCURRED_$$k.sum);
    _WRITE_READ_BENIGN_FLAG_$$k.sum := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$k.sum == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$k.sum);
    return;
}

procedure _CHECK_WRITE_$$k.sum(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$k.sum && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$k.sum != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$k.sum && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$k.sum != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$k.sum && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$k.sum(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$k.sum;

implementation {:inline 1} _LOG_ATOMIC_$$k.sum(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$k.sum := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$k.sum);
    return;
}

procedure _CHECK_ATOMIC_$$k.sum(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$k.sum && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$k.sum && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$k.sum(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$k.sum;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$k.sum(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$k.sum := (if _P && _WRITE_HAS_OCCURRED_$$k.sum && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$k.sum);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
