//#Unsafe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP8(x: [bv32]bv8, y: bv32) returns (z$1: bv8, A$1: [bv32]bv8, z$2: bv8, A$2: [bv32]bv8);

axiom {:array_info "$$in"} {:global} {:elem_width 8} {:source_name "in"} {:source_elem_width 48} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 48} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$in: bool;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 48} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$in: bool;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 48} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$in: bool;

var {:source_name "out"} {:global} $$out: [bv32]bv8;

axiom {:array_info "$$out"} {:global} {:elem_width 8} {:source_name "out"} {:source_elem_width 48} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 48} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$out: bool;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 48} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$out: bool;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 48} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$out: bool;

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

procedure {:source_name "k"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$in && !_WRITE_HAS_OCCURRED_$$in && !_ATOMIC_HAS_OCCURRED_$$in;
  requires !_READ_HAS_OCCURRED_$$out && !_WRITE_HAS_OCCURRED_$$out && !_ATOMIC_HAS_OCCURRED_$$out;
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
  modifies _WRITE_HAS_OCCURRED_$$out, _WRITE_READ_BENIGN_FLAG_$$out, _WRITE_READ_BENIGN_FLAG_$$out;

implementation {:source_name "k"} ULTIMATE.start()
{
  var v0$1: bv8;
  var v0$2: bv8;
  var v1$1: bv8;
  var v1$2: bv8;
  var v2$1: bv8;
  var v2$2: bv8;
  var v3$1: bv8;
  var v3$2: bv8;
  var v4$1: bv8;
  var v4$2: bv8;
  var v5$1: bv8;
  var v5$2: bv8;
  var v6$1: bv8;
  var v6$2: bv8;
  var v7$1: bv8;
  var v7$2: bv8;
  var v8$1: bv8;
  var v8$2: bv8;
  var v9$1: bv8;
  var v9$2: bv8;
  var v10$1: bv8;
  var v10$2: bv8;
  var v11$1: bv8;
  var v11$2: bv8;

  $entry:
    havoc v0$1, v0$2;
    call _LOG_WRITE_$$out(true, BV32_MUL(local_id_x$1, 6bv32), v0$1, $$out[BV32_MUL(local_id_x$1, 6bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out(true, BV32_MUL(local_id_x$2, 6bv32));
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 2} true;
    call _CHECK_WRITE_$$out(true, BV32_MUL(local_id_x$2, 6bv32), v0$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out"} true;
    $$out[BV32_MUL(local_id_x$1, 6bv32)] := v0$1;
    $$out[BV32_MUL(local_id_x$2, 6bv32)] := v0$2;
    havoc v1$1, v1$2;
    call _LOG_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 1bv32), v1$1, $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 4} true;
    call _CHECK_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 1bv32), v1$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out"} true;
    $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 1bv32)] := v1$1;
    $$out[BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 1bv32)] := v1$2;
    havoc v2$1, v2$2;
    call _LOG_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 2bv32), v2$1, $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 2bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 2bv32));
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 6} true;
    call _CHECK_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 2bv32), v2$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out"} true;
    $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 2bv32)] := v2$1;
    $$out[BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 2bv32)] := v2$2;
    havoc v3$1, v3$2;
    call _LOG_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 3bv32), v3$1, $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 3bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 3bv32));
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 8} true;
    call _CHECK_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 3bv32), v3$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out"} true;
    $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 3bv32)] := v3$1;
    $$out[BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 3bv32)] := v3$2;
    havoc v4$1, v4$2;
    call _LOG_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 4bv32), v4$1, $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 4bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 4bv32));
    assume {:do_not_predicate} {:check_id "check_state_4"} {:captureState "check_state_4"} {:sourceloc} {:sourceloc_num 10} true;
    call _CHECK_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 4bv32), v4$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out"} true;
    $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 4bv32)] := v4$1;
    $$out[BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 4bv32)] := v4$2;
    havoc v5$1, v5$2;
    call _LOG_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 5bv32), v5$1, $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 5bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 5bv32));
    assume {:do_not_predicate} {:check_id "check_state_5"} {:captureState "check_state_5"} {:sourceloc} {:sourceloc_num 12} true;
    call _CHECK_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 5bv32), v5$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out"} true;
    $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 5bv32)] := v5$1;
    $$out[BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 5bv32)] := v5$2;
    havoc v6$1, v6$2;
    call _LOG_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 6bv32), v6$1, $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 6bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 6bv32));
    assume {:do_not_predicate} {:check_id "check_state_6"} {:captureState "check_state_6"} {:sourceloc} {:sourceloc_num 14} true;
    call _CHECK_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 6bv32), v6$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out"} true;
    $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 6bv32)] := v6$1;
    $$out[BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 6bv32)] := v6$2;
    havoc v7$1, v7$2;
    call _LOG_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 7bv32), v7$1, $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 7bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 7bv32));
    assume {:do_not_predicate} {:check_id "check_state_7"} {:captureState "check_state_7"} {:sourceloc} {:sourceloc_num 16} true;
    call _CHECK_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 7bv32), v7$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out"} true;
    $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 7bv32)] := v7$1;
    $$out[BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 7bv32)] := v7$2;
    havoc v8$1, v8$2;
    call _LOG_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 8bv32), v8$1, $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 8bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 8bv32));
    assume {:do_not_predicate} {:check_id "check_state_8"} {:captureState "check_state_8"} {:sourceloc} {:sourceloc_num 18} true;
    call _CHECK_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 8bv32), v8$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out"} true;
    $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 8bv32)] := v8$1;
    $$out[BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 8bv32)] := v8$2;
    havoc v9$1, v9$2;
    call _LOG_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 9bv32), v9$1, $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 9bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 9bv32));
    assume {:do_not_predicate} {:check_id "check_state_9"} {:captureState "check_state_9"} {:sourceloc} {:sourceloc_num 20} true;
    call _CHECK_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 9bv32), v9$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out"} true;
    $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 9bv32)] := v9$1;
    $$out[BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 9bv32)] := v9$2;
    havoc v10$1, v10$2;
    call _LOG_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 10bv32), v10$1, $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 10bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 10bv32));
    assume {:do_not_predicate} {:check_id "check_state_10"} {:captureState "check_state_10"} {:sourceloc} {:sourceloc_num 22} true;
    call _CHECK_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 10bv32), v10$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out"} true;
    $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 10bv32)] := v10$1;
    $$out[BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 10bv32)] := v10$2;
    havoc v11$1, v11$2;
    call _LOG_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 11bv32), v11$1, $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 11bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 11bv32));
    assume {:do_not_predicate} {:check_id "check_state_11"} {:captureState "check_state_11"} {:sourceloc} {:sourceloc_num 24} true;
    call _CHECK_WRITE_$$out(true, BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 11bv32), v11$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out"} true;
    $$out[BV32_ADD(BV32_MUL(local_id_x$1, 6bv32), 11bv32)] := v11$1;
    $$out[BV32_ADD(BV32_MUL(local_id_x$2, 6bv32), 11bv32)] := v11$2;
    return;
}

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

const _WATCHED_VALUE_$$in: bv8;

procedure {:inline 1} _LOG_READ_$$in(_P: bool, _offset: bv32, _value: bv8);
  modifies _READ_HAS_OCCURRED_$$in;

implementation {:inline 1} _LOG_READ_$$in(_P: bool, _offset: bv32, _value: bv8)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$in := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$in == _value then true else _READ_HAS_OCCURRED_$$in);
    return;
}

procedure _CHECK_READ_$$in(_P: bool, _offset: bv32, _value: bv8);
  requires !(_P && _WRITE_HAS_OCCURRED_$$in && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$in);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$in && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$in: bool;

procedure {:inline 1} _LOG_WRITE_$$in(_P: bool, _offset: bv32, _value: bv8, _value_old: bv8);
  modifies _WRITE_HAS_OCCURRED_$$in, _WRITE_READ_BENIGN_FLAG_$$in;

implementation {:inline 1} _LOG_WRITE_$$in(_P: bool, _offset: bv32, _value: bv8, _value_old: bv8)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$in := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$in == _value then true else _WRITE_HAS_OCCURRED_$$in);
    _WRITE_READ_BENIGN_FLAG_$$in := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$in == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$in);
    return;
}

procedure _CHECK_WRITE_$$in(_P: bool, _offset: bv32, _value: bv8);
  requires !(_P && _WRITE_HAS_OCCURRED_$$in && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$in != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$in && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$in != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$in && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$in(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$in;

implementation {:inline 1} _LOG_ATOMIC_$$in(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$in := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$in);
    return;
}

procedure _CHECK_ATOMIC_$$in(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$in && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$in && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$in(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$in;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$in(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$in := (if _P && _WRITE_HAS_OCCURRED_$$in && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$in);
    return;
}

const _WATCHED_VALUE_$$out: bv8;

procedure {:inline 1} _LOG_READ_$$out(_P: bool, _offset: bv32, _value: bv8);
  modifies _READ_HAS_OCCURRED_$$out;

implementation {:inline 1} _LOG_READ_$$out(_P: bool, _offset: bv32, _value: bv8)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$out := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$out == _value then true else _READ_HAS_OCCURRED_$$out);
    return;
}

procedure _CHECK_READ_$$out(_P: bool, _offset: bv32, _value: bv8);
  requires !(_P && _WRITE_HAS_OCCURRED_$$out && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$out);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$out && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$out: bool;

procedure {:inline 1} _LOG_WRITE_$$out(_P: bool, _offset: bv32, _value: bv8, _value_old: bv8);
  modifies _WRITE_HAS_OCCURRED_$$out, _WRITE_READ_BENIGN_FLAG_$$out;

implementation {:inline 1} _LOG_WRITE_$$out(_P: bool, _offset: bv32, _value: bv8, _value_old: bv8)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$out := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$out == _value then true else _WRITE_HAS_OCCURRED_$$out);
    _WRITE_READ_BENIGN_FLAG_$$out := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$out == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$out);
    return;
}

procedure _CHECK_WRITE_$$out(_P: bool, _offset: bv32, _value: bv8);
  requires !(_P && _WRITE_HAS_OCCURRED_$$out && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$out != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$out && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$out != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$out && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$out(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$out;

implementation {:inline 1} _LOG_ATOMIC_$$out(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$out := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$out);
    return;
}

procedure _CHECK_ATOMIC_$$out(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$out && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$out && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$out(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$out;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$out(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$out := (if _P && _WRITE_HAS_OCCURRED_$$out && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$out);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
