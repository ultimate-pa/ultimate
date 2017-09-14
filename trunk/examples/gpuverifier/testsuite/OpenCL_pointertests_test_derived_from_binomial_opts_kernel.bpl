//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

axiom {:array_info "$$s"} {:global} {:elem_width 32} {:source_name "s"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$s: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$s: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$s: bool;

axiom {:array_info "$$x"} {:global} {:elem_width 32} {:source_name "x"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$x: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$x: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$x: bool;

axiom {:array_info "$$vdt"} {:global} {:elem_width 32} {:source_name "vdt"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$vdt: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$vdt: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$vdt: bool;

axiom {:array_info "$$pu_by_df"} {:global} {:elem_width 32} {:source_name "pu_by_df"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$pu_by_df: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$pu_by_df: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$pu_by_df: bool;

axiom {:array_info "$$pd_by_df"} {:global} {:elem_width 32} {:source_name "pd_by_df"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$pd_by_df: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$pd_by_df: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$pd_by_df: bool;

axiom {:array_info "$$call_value"} {:global} {:elem_width 32} {:source_name "call_value"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$call_value: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$call_value: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$call_value: bool;

axiom {:array_info "$$call_buffer"} {:global} {:elem_width 32} {:source_name "call_buffer"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$call_buffer: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$call_buffer: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$call_buffer: bool;

const _WATCHED_OFFSET: bv32;

const {:global_offset_x} global_offset_x: bv32;

const {:global_offset_y} global_offset_y: bv32;

const {:global_offset_z} global_offset_z: bv32;

const {:group_size_x} group_size_x: bv32;

const {:group_size_y} group_size_y: bv32;

const {:group_size_z} group_size_z: bv32;

const {:num_groups_x} num_groups_x: bv32;

const {:num_groups_y} num_groups_y: bv32;

const {:num_groups_z} num_groups_z: bv32;

procedure {:source_name "binomial_options_kernel"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$s && !_WRITE_HAS_OCCURRED_$$s && !_ATOMIC_HAS_OCCURRED_$$s;
  requires !_READ_HAS_OCCURRED_$$x && !_WRITE_HAS_OCCURRED_$$x && !_ATOMIC_HAS_OCCURRED_$$x;
  requires !_READ_HAS_OCCURRED_$$vdt && !_WRITE_HAS_OCCURRED_$$vdt && !_ATOMIC_HAS_OCCURRED_$$vdt;
  requires !_READ_HAS_OCCURRED_$$pu_by_df && !_WRITE_HAS_OCCURRED_$$pu_by_df && !_ATOMIC_HAS_OCCURRED_$$pu_by_df;
  requires !_READ_HAS_OCCURRED_$$pd_by_df && !_WRITE_HAS_OCCURRED_$$pd_by_df && !_ATOMIC_HAS_OCCURRED_$$pd_by_df;
  requires !_READ_HAS_OCCURRED_$$call_value && !_WRITE_HAS_OCCURRED_$$call_value && !_ATOMIC_HAS_OCCURRED_$$call_value;
  requires !_READ_HAS_OCCURRED_$$call_buffer && !_WRITE_HAS_OCCURRED_$$call_buffer && !_ATOMIC_HAS_OCCURRED_$$call_buffer;
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

implementation {:source_name "binomial_options_kernel"} ULTIMATE.start()
{

  $entry:
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

const {:local_id_x} local_id_x$1: bv32;

const {:local_id_x} local_id_x$2: bv32;

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

const _WATCHED_VALUE_$$s: bv32;

procedure {:inline 1} _LOG_READ_$$s(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$s;

implementation {:inline 1} _LOG_READ_$$s(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$s := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$s == _value then true else _READ_HAS_OCCURRED_$$s);
    return;
}

procedure _CHECK_READ_$$s(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$s && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$s);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$s && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$s: bool;

procedure {:inline 1} _LOG_WRITE_$$s(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$s, _WRITE_READ_BENIGN_FLAG_$$s;

implementation {:inline 1} _LOG_WRITE_$$s(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$s := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$s == _value then true else _WRITE_HAS_OCCURRED_$$s);
    _WRITE_READ_BENIGN_FLAG_$$s := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$s == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$s);
    return;
}

procedure _CHECK_WRITE_$$s(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$s && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$s != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$s && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$s != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$s && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$s(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$s;

implementation {:inline 1} _LOG_ATOMIC_$$s(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$s := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$s);
    return;
}

procedure _CHECK_ATOMIC_$$s(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$s && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$s && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$s(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$s;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$s(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$s := (if _P && _WRITE_HAS_OCCURRED_$$s && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$s);
    return;
}

const _WATCHED_VALUE_$$x: bv32;

procedure {:inline 1} _LOG_READ_$$x(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$x;

implementation {:inline 1} _LOG_READ_$$x(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$x := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$x == _value then true else _READ_HAS_OCCURRED_$$x);
    return;
}

procedure _CHECK_READ_$$x(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$x && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$x);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$x && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$x: bool;

procedure {:inline 1} _LOG_WRITE_$$x(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$x, _WRITE_READ_BENIGN_FLAG_$$x;

implementation {:inline 1} _LOG_WRITE_$$x(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$x := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$x == _value then true else _WRITE_HAS_OCCURRED_$$x);
    _WRITE_READ_BENIGN_FLAG_$$x := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$x == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$x);
    return;
}

procedure _CHECK_WRITE_$$x(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$x && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$x != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$x && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$x != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$x && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$x(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$x;

implementation {:inline 1} _LOG_ATOMIC_$$x(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$x := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$x);
    return;
}

procedure _CHECK_ATOMIC_$$x(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$x && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$x && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$x(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$x;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$x(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$x := (if _P && _WRITE_HAS_OCCURRED_$$x && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$x);
    return;
}

const _WATCHED_VALUE_$$vdt: bv32;

procedure {:inline 1} _LOG_READ_$$vdt(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$vdt;

implementation {:inline 1} _LOG_READ_$$vdt(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$vdt := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$vdt == _value then true else _READ_HAS_OCCURRED_$$vdt);
    return;
}

procedure _CHECK_READ_$$vdt(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$vdt && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$vdt);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$vdt && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$vdt: bool;

procedure {:inline 1} _LOG_WRITE_$$vdt(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$vdt, _WRITE_READ_BENIGN_FLAG_$$vdt;

implementation {:inline 1} _LOG_WRITE_$$vdt(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$vdt := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$vdt == _value then true else _WRITE_HAS_OCCURRED_$$vdt);
    _WRITE_READ_BENIGN_FLAG_$$vdt := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$vdt == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$vdt);
    return;
}

procedure _CHECK_WRITE_$$vdt(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$vdt && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$vdt != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$vdt && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$vdt != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$vdt && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$vdt(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$vdt;

implementation {:inline 1} _LOG_ATOMIC_$$vdt(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$vdt := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$vdt);
    return;
}

procedure _CHECK_ATOMIC_$$vdt(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$vdt && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$vdt && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$vdt(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$vdt;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$vdt(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$vdt := (if _P && _WRITE_HAS_OCCURRED_$$vdt && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$vdt);
    return;
}

const _WATCHED_VALUE_$$pu_by_df: bv32;

procedure {:inline 1} _LOG_READ_$$pu_by_df(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$pu_by_df;

implementation {:inline 1} _LOG_READ_$$pu_by_df(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$pu_by_df := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$pu_by_df == _value then true else _READ_HAS_OCCURRED_$$pu_by_df);
    return;
}

procedure _CHECK_READ_$$pu_by_df(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$pu_by_df && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$pu_by_df);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$pu_by_df && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$pu_by_df: bool;

procedure {:inline 1} _LOG_WRITE_$$pu_by_df(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$pu_by_df, _WRITE_READ_BENIGN_FLAG_$$pu_by_df;

implementation {:inline 1} _LOG_WRITE_$$pu_by_df(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$pu_by_df := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$pu_by_df == _value then true else _WRITE_HAS_OCCURRED_$$pu_by_df);
    _WRITE_READ_BENIGN_FLAG_$$pu_by_df := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$pu_by_df == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$pu_by_df);
    return;
}

procedure _CHECK_WRITE_$$pu_by_df(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$pu_by_df && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$pu_by_df != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$pu_by_df && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$pu_by_df != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$pu_by_df && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$pu_by_df(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$pu_by_df;

implementation {:inline 1} _LOG_ATOMIC_$$pu_by_df(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$pu_by_df := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$pu_by_df);
    return;
}

procedure _CHECK_ATOMIC_$$pu_by_df(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$pu_by_df && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$pu_by_df && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$pu_by_df(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$pu_by_df;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$pu_by_df(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$pu_by_df := (if _P && _WRITE_HAS_OCCURRED_$$pu_by_df && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$pu_by_df);
    return;
}

const _WATCHED_VALUE_$$pd_by_df: bv32;

procedure {:inline 1} _LOG_READ_$$pd_by_df(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$pd_by_df;

implementation {:inline 1} _LOG_READ_$$pd_by_df(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$pd_by_df := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$pd_by_df == _value then true else _READ_HAS_OCCURRED_$$pd_by_df);
    return;
}

procedure _CHECK_READ_$$pd_by_df(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$pd_by_df && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$pd_by_df);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$pd_by_df && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$pd_by_df: bool;

procedure {:inline 1} _LOG_WRITE_$$pd_by_df(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$pd_by_df, _WRITE_READ_BENIGN_FLAG_$$pd_by_df;

implementation {:inline 1} _LOG_WRITE_$$pd_by_df(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$pd_by_df := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$pd_by_df == _value then true else _WRITE_HAS_OCCURRED_$$pd_by_df);
    _WRITE_READ_BENIGN_FLAG_$$pd_by_df := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$pd_by_df == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$pd_by_df);
    return;
}

procedure _CHECK_WRITE_$$pd_by_df(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$pd_by_df && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$pd_by_df != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$pd_by_df && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$pd_by_df != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$pd_by_df && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$pd_by_df(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$pd_by_df;

implementation {:inline 1} _LOG_ATOMIC_$$pd_by_df(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$pd_by_df := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$pd_by_df);
    return;
}

procedure _CHECK_ATOMIC_$$pd_by_df(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$pd_by_df && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$pd_by_df && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$pd_by_df(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$pd_by_df;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$pd_by_df(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$pd_by_df := (if _P && _WRITE_HAS_OCCURRED_$$pd_by_df && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$pd_by_df);
    return;
}

const _WATCHED_VALUE_$$call_value: bv32;

procedure {:inline 1} _LOG_READ_$$call_value(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$call_value;

implementation {:inline 1} _LOG_READ_$$call_value(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$call_value := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$call_value == _value then true else _READ_HAS_OCCURRED_$$call_value);
    return;
}

procedure _CHECK_READ_$$call_value(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$call_value && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$call_value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$call_value && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$call_value: bool;

procedure {:inline 1} _LOG_WRITE_$$call_value(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$call_value, _WRITE_READ_BENIGN_FLAG_$$call_value;

implementation {:inline 1} _LOG_WRITE_$$call_value(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$call_value := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$call_value == _value then true else _WRITE_HAS_OCCURRED_$$call_value);
    _WRITE_READ_BENIGN_FLAG_$$call_value := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$call_value == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$call_value);
    return;
}

procedure _CHECK_WRITE_$$call_value(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$call_value && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$call_value != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$call_value && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$call_value != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$call_value && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$call_value(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$call_value;

implementation {:inline 1} _LOG_ATOMIC_$$call_value(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$call_value := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$call_value);
    return;
}

procedure _CHECK_ATOMIC_$$call_value(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$call_value && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$call_value && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$call_value(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$call_value;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$call_value(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$call_value := (if _P && _WRITE_HAS_OCCURRED_$$call_value && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$call_value);
    return;
}

const _WATCHED_VALUE_$$call_buffer: bv32;

procedure {:inline 1} _LOG_READ_$$call_buffer(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$call_buffer;

implementation {:inline 1} _LOG_READ_$$call_buffer(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$call_buffer := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$call_buffer == _value then true else _READ_HAS_OCCURRED_$$call_buffer);
    return;
}

procedure _CHECK_READ_$$call_buffer(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$call_buffer && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$call_buffer);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$call_buffer && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$call_buffer: bool;

procedure {:inline 1} _LOG_WRITE_$$call_buffer(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$call_buffer, _WRITE_READ_BENIGN_FLAG_$$call_buffer;

implementation {:inline 1} _LOG_WRITE_$$call_buffer(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$call_buffer := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$call_buffer == _value then true else _WRITE_HAS_OCCURRED_$$call_buffer);
    _WRITE_READ_BENIGN_FLAG_$$call_buffer := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$call_buffer == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$call_buffer);
    return;
}

procedure _CHECK_WRITE_$$call_buffer(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$call_buffer && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$call_buffer != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$call_buffer && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$call_buffer != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$call_buffer && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$call_buffer(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$call_buffer;

implementation {:inline 1} _LOG_ATOMIC_$$call_buffer(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$call_buffer := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$call_buffer);
    return;
}

procedure _CHECK_ATOMIC_$$call_buffer(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$call_buffer && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$call_buffer && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$call_buffer(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$call_buffer;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$call_buffer(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$call_buffer := (if _P && _WRITE_HAS_OCCURRED_$$call_buffer && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$call_buffer);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
