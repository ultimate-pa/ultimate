//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "acc"} {:global} $$acc: [bv32]bv32;

axiom {:array_info "$$acc"} {:global} {:elem_width 32} {:source_name "acc"} {:source_elem_width 128} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$acc: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$acc: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$acc: bool;

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

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

procedure {:source_name "foo"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$acc && !_WRITE_HAS_OCCURRED_$$acc && !_ATOMIC_HAS_OCCURRED_$$acc;
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
  modifies _WRITE_HAS_OCCURRED_$$acc, _WRITE_READ_BENIGN_FLAG_$$acc, _WRITE_READ_BENIGN_FLAG_$$acc;

implementation {:source_name "foo"} ULTIMATE.start()
{

  $entry:
    call _LOG_WRITE_$$acc(true, BV32_MUL(local_id_x$1, 4bv32), 1065353216bv32, $$acc[BV32_MUL(local_id_x$1, 4bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$acc(true, BV32_MUL(local_id_x$2, 4bv32));
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 1} true;
    call _CHECK_WRITE_$$acc(true, BV32_MUL(local_id_x$2, 4bv32), 1065353216bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$acc"} true;
    $$acc[BV32_MUL(local_id_x$1, 4bv32)] := 1065353216bv32;
    $$acc[BV32_MUL(local_id_x$2, 4bv32)] := 1065353216bv32;
    call _LOG_WRITE_$$acc(true, BV32_ADD(BV32_MUL(local_id_x$1, 4bv32), 1bv32), 1073741824bv32, $$acc[BV32_ADD(BV32_MUL(local_id_x$1, 4bv32), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$acc(true, BV32_ADD(BV32_MUL(local_id_x$2, 4bv32), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 2} true;
    call _CHECK_WRITE_$$acc(true, BV32_ADD(BV32_MUL(local_id_x$2, 4bv32), 1bv32), 1073741824bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$acc"} true;
    $$acc[BV32_ADD(BV32_MUL(local_id_x$1, 4bv32), 1bv32)] := 1073741824bv32;
    $$acc[BV32_ADD(BV32_MUL(local_id_x$2, 4bv32), 1bv32)] := 1073741824bv32;
    call _LOG_WRITE_$$acc(true, BV32_ADD(BV32_MUL(local_id_x$1, 4bv32), 2bv32), 1077936128bv32, $$acc[BV32_ADD(BV32_MUL(local_id_x$1, 4bv32), 2bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$acc(true, BV32_ADD(BV32_MUL(local_id_x$2, 4bv32), 2bv32));
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 3} true;
    call _CHECK_WRITE_$$acc(true, BV32_ADD(BV32_MUL(local_id_x$2, 4bv32), 2bv32), 1077936128bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$acc"} true;
    $$acc[BV32_ADD(BV32_MUL(local_id_x$1, 4bv32), 2bv32)] := 1077936128bv32;
    $$acc[BV32_ADD(BV32_MUL(local_id_x$2, 4bv32), 2bv32)] := 1077936128bv32;
    call _LOG_WRITE_$$acc(true, BV32_ADD(BV32_MUL(local_id_x$1, 4bv32), 3bv32), 1082130432bv32, $$acc[BV32_ADD(BV32_MUL(local_id_x$1, 4bv32), 3bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$acc(true, BV32_ADD(BV32_MUL(local_id_x$2, 4bv32), 3bv32));
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 4} true;
    call _CHECK_WRITE_$$acc(true, BV32_ADD(BV32_MUL(local_id_x$2, 4bv32), 3bv32), 1082130432bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$acc"} true;
    $$acc[BV32_ADD(BV32_MUL(local_id_x$1, 4bv32), 3bv32)] := 1082130432bv32;
    $$acc[BV32_ADD(BV32_MUL(local_id_x$2, 4bv32), 3bv32)] := 1082130432bv32;
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

const _WATCHED_VALUE_$$acc: bv32;

procedure {:inline 1} _LOG_READ_$$acc(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$acc;

implementation {:inline 1} _LOG_READ_$$acc(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$acc := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$acc == _value then true else _READ_HAS_OCCURRED_$$acc);
    return;
}

procedure _CHECK_READ_$$acc(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$acc && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$acc);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$acc && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$acc: bool;

procedure {:inline 1} _LOG_WRITE_$$acc(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$acc, _WRITE_READ_BENIGN_FLAG_$$acc;

implementation {:inline 1} _LOG_WRITE_$$acc(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$acc := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$acc == _value then true else _WRITE_HAS_OCCURRED_$$acc);
    _WRITE_READ_BENIGN_FLAG_$$acc := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$acc == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$acc);
    return;
}

procedure _CHECK_WRITE_$$acc(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$acc && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$acc != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$acc && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$acc != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$acc && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$acc(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$acc;

implementation {:inline 1} _LOG_ATOMIC_$$acc(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$acc := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$acc);
    return;
}

procedure _CHECK_ATOMIC_$$acc(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$acc && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$acc && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$acc(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$acc;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$acc(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$acc := (if _P && _WRITE_HAS_OCCURRED_$$acc && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$acc);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
