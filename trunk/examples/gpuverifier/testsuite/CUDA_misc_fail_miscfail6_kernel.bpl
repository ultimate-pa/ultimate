//#Unsafe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP64(x: [bv32]bv64, y: bv32) returns (z$1: bv64, A$1: [bv32]bv64, z$2: bv64, A$2: [bv32]bv64);

axiom {:array_info "$$H"} {:global} {:elem_width 64} {:source_name "H"} {:source_elem_width 64} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 64} {:source_elem_width 64} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$H: bool;

var {:race_checking} {:global} {:elem_width 64} {:source_elem_width 64} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$H: bool;

var {:race_checking} {:global} {:elem_width 64} {:source_elem_width 64} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$H: bool;

var {:source_name "C"} {:global} $$C: [bv32]bv64;

axiom {:array_info "$$C"} {:global} {:elem_width 64} {:source_name "C"} {:source_elem_width 64} {:source_dimensions "1024,0,1024"} true;

var {:race_checking} {:global} {:elem_width 64} {:source_elem_width 64} {:source_dimensions "*,0,1024"} _READ_HAS_OCCURRED_$$C: bool;

var {:race_checking} {:global} {:elem_width 64} {:source_elem_width 64} {:source_dimensions "*,0,1024"} _WRITE_HAS_OCCURRED_$$C: bool;

var {:race_checking} {:global} {:elem_width 64} {:source_elem_width 64} {:source_dimensions "*,0,1024"} _ATOMIC_HAS_OCCURRED_$$C: bool;

const _WATCHED_OFFSET: bv32;

const {:group_size_x} group_size_x: bv32;

const {:group_size_y} group_size_y: bv32;

const {:group_size_z} group_size_z: bv32;

const {:local_id_x} local_id_x$1: bv32;

const {:local_id_x} local_id_x$2: bv32;

const {:local_id_y} local_id_y$1: bv32;

const {:local_id_y} local_id_y$2: bv32;

const {:local_id_z} local_id_z$1: bv32;

const {:local_id_z} local_id_z$2: bv32;

const {:num_groups_x} num_groups_x: bv32;

const {:num_groups_y} num_groups_y: bv32;

const {:num_groups_z} num_groups_z: bv32;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

procedure {:source_name "foo"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$H && !_WRITE_HAS_OCCURRED_$$H && !_ATOMIC_HAS_OCCURRED_$$H;
  requires !_READ_HAS_OCCURRED_$$C && !_WRITE_HAS_OCCURRED_$$C && !_ATOMIC_HAS_OCCURRED_$$C;
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
  modifies _WRITE_HAS_OCCURRED_$$C, _WRITE_READ_BENIGN_FLAG_$$C, _WRITE_READ_BENIGN_FLAG_$$C;

implementation {:source_name "foo"} ULTIMATE.start()
{
  var v0$1: bv64;
  var v0$2: bv64;

  $entry:
    havoc v0$1, v0$2;
    call _LOG_WRITE_$$C(true, BV32_ADD(BV32_ADD(BV32_MUL(local_id_x$1, 0bv32), BV32_MUL(local_id_y$1, 1024bv32)), local_id_z$1), v0$1, $$C[BV32_ADD(BV32_ADD(BV32_MUL(local_id_x$1, 0bv32), BV32_MUL(local_id_y$1, 1024bv32)), local_id_z$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$C(true, BV32_ADD(BV32_ADD(BV32_MUL(local_id_x$2, 0bv32), BV32_MUL(local_id_y$2, 1024bv32)), local_id_z$2));
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 2} true;
    call _CHECK_WRITE_$$C(true, BV32_ADD(BV32_ADD(BV32_MUL(local_id_x$2, 0bv32), BV32_MUL(local_id_y$2, 1024bv32)), local_id_z$2), v0$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$C"} true;
    $$C[BV32_ADD(BV32_ADD(BV32_MUL(local_id_x$1, 0bv32), BV32_MUL(local_id_y$1, 1024bv32)), local_id_z$1)] := v0$1;
    $$C[BV32_ADD(BV32_ADD(BV32_MUL(local_id_x$2, 0bv32), BV32_MUL(local_id_y$2, 1024bv32)), local_id_z$2)] := v0$2;
    return;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 1024bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 1024bv32 then 1bv1 else 0bv1) != 0bv1;

const {:group_id_x} group_id_x$1: bv32;

const {:group_id_x} group_id_x$2: bv32;

const {:group_id_y} group_id_y$1: bv32;

const {:group_id_y} group_id_y$2: bv32;

const {:group_id_z} group_id_z$1: bv32;

const {:group_id_z} group_id_z$2: bv32;

const _WATCHED_VALUE_$$H: bv64;

procedure {:inline 1} _LOG_READ_$$H(_P: bool, _offset: bv32, _value: bv64);
  modifies _READ_HAS_OCCURRED_$$H;

implementation {:inline 1} _LOG_READ_$$H(_P: bool, _offset: bv32, _value: bv64)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$H := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$H == _value then true else _READ_HAS_OCCURRED_$$H);
    return;
}

procedure _CHECK_READ_$$H(_P: bool, _offset: bv32, _value: bv64);
  requires !(_P && _WRITE_HAS_OCCURRED_$$H && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$H);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$H && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$H: bool;

procedure {:inline 1} _LOG_WRITE_$$H(_P: bool, _offset: bv32, _value: bv64, _value_old: bv64);
  modifies _WRITE_HAS_OCCURRED_$$H, _WRITE_READ_BENIGN_FLAG_$$H;

implementation {:inline 1} _LOG_WRITE_$$H(_P: bool, _offset: bv32, _value: bv64, _value_old: bv64)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$H := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$H == _value then true else _WRITE_HAS_OCCURRED_$$H);
    _WRITE_READ_BENIGN_FLAG_$$H := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$H == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$H);
    return;
}

procedure _CHECK_WRITE_$$H(_P: bool, _offset: bv32, _value: bv64);
  requires !(_P && _WRITE_HAS_OCCURRED_$$H && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$H != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$H && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$H != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$H && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$H(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$H;

implementation {:inline 1} _LOG_ATOMIC_$$H(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$H := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$H);
    return;
}

procedure _CHECK_ATOMIC_$$H(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$H && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$H && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$H(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$H;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$H(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$H := (if _P && _WRITE_HAS_OCCURRED_$$H && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$H);
    return;
}

const _WATCHED_VALUE_$$C: bv64;

procedure {:inline 1} _LOG_READ_$$C(_P: bool, _offset: bv32, _value: bv64);
  modifies _READ_HAS_OCCURRED_$$C;

implementation {:inline 1} _LOG_READ_$$C(_P: bool, _offset: bv32, _value: bv64)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$C := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$C == _value then true else _READ_HAS_OCCURRED_$$C);
    return;
}

procedure _CHECK_READ_$$C(_P: bool, _offset: bv32, _value: bv64);
  requires !(_P && _WRITE_HAS_OCCURRED_$$C && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$C);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$C && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$C: bool;

procedure {:inline 1} _LOG_WRITE_$$C(_P: bool, _offset: bv32, _value: bv64, _value_old: bv64);
  modifies _WRITE_HAS_OCCURRED_$$C, _WRITE_READ_BENIGN_FLAG_$$C;

implementation {:inline 1} _LOG_WRITE_$$C(_P: bool, _offset: bv32, _value: bv64, _value_old: bv64)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$C := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$C == _value then true else _WRITE_HAS_OCCURRED_$$C);
    _WRITE_READ_BENIGN_FLAG_$$C := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$C == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$C);
    return;
}

procedure _CHECK_WRITE_$$C(_P: bool, _offset: bv32, _value: bv64);
  requires !(_P && _WRITE_HAS_OCCURRED_$$C && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$C != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$C && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$C != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$C && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$C(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$C;

implementation {:inline 1} _LOG_ATOMIC_$$C(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$C := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$C);
    return;
}

procedure _CHECK_ATOMIC_$$C(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$C && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$C && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$C(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$C;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$C(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$C := (if _P && _WRITE_HAS_OCCURRED_$$C && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$C);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
