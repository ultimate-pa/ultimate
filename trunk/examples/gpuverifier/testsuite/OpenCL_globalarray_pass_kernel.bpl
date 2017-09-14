//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "p"} {:global} $$p: [bv32]bv32;

axiom {:array_info "$$p"} {:global} {:elem_width 32} {:source_name "p"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$p: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$p: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$p: bool;

var {:source_name "A"} {:constant} $$A$1: [bv32]bv32;

var {:source_name "A"} {:constant} $$A$2: [bv32]bv32;

axiom {:array_info "$$A"} {:constant} {:elem_width 32} {:source_name "A"} {:source_elem_width 32} {:source_dimensions "64"} true;

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

procedure {:source_name "globalarray"} ULTIMATE.start();
  requires $$A$1[0bv32] == 0bv32;
  requires $$A$2[0bv32] == 0bv32;
  requires $$A$1[1bv32] == 0bv32;
  requires $$A$2[1bv32] == 0bv32;
  requires $$A$1[2bv32] == 0bv32;
  requires $$A$2[2bv32] == 0bv32;
  requires $$A$1[3bv32] == 0bv32;
  requires $$A$2[3bv32] == 0bv32;
  requires $$A$1[4bv32] == 0bv32;
  requires $$A$2[4bv32] == 0bv32;
  requires $$A$1[5bv32] == 0bv32;
  requires $$A$2[5bv32] == 0bv32;
  requires $$A$1[6bv32] == 0bv32;
  requires $$A$2[6bv32] == 0bv32;
  requires $$A$1[7bv32] == 0bv32;
  requires $$A$2[7bv32] == 0bv32;
  requires $$A$1[8bv32] == 0bv32;
  requires $$A$2[8bv32] == 0bv32;
  requires $$A$1[9bv32] == 0bv32;
  requires $$A$2[9bv32] == 0bv32;
  requires $$A$1[10bv32] == 0bv32;
  requires $$A$2[10bv32] == 0bv32;
  requires $$A$1[11bv32] == 0bv32;
  requires $$A$2[11bv32] == 0bv32;
  requires $$A$1[12bv32] == 0bv32;
  requires $$A$2[12bv32] == 0bv32;
  requires $$A$1[13bv32] == 0bv32;
  requires $$A$2[13bv32] == 0bv32;
  requires $$A$1[14bv32] == 0bv32;
  requires $$A$2[14bv32] == 0bv32;
  requires $$A$1[15bv32] == 0bv32;
  requires $$A$2[15bv32] == 0bv32;
  requires $$A$1[16bv32] == 0bv32;
  requires $$A$2[16bv32] == 0bv32;
  requires $$A$1[17bv32] == 0bv32;
  requires $$A$2[17bv32] == 0bv32;
  requires $$A$1[18bv32] == 0bv32;
  requires $$A$2[18bv32] == 0bv32;
  requires $$A$1[19bv32] == 0bv32;
  requires $$A$2[19bv32] == 0bv32;
  requires $$A$1[20bv32] == 0bv32;
  requires $$A$2[20bv32] == 0bv32;
  requires $$A$1[21bv32] == 0bv32;
  requires $$A$2[21bv32] == 0bv32;
  requires $$A$1[22bv32] == 0bv32;
  requires $$A$2[22bv32] == 0bv32;
  requires $$A$1[23bv32] == 0bv32;
  requires $$A$2[23bv32] == 0bv32;
  requires $$A$1[24bv32] == 0bv32;
  requires $$A$2[24bv32] == 0bv32;
  requires $$A$1[25bv32] == 0bv32;
  requires $$A$2[25bv32] == 0bv32;
  requires $$A$1[26bv32] == 0bv32;
  requires $$A$2[26bv32] == 0bv32;
  requires $$A$1[27bv32] == 0bv32;
  requires $$A$2[27bv32] == 0bv32;
  requires $$A$1[28bv32] == 0bv32;
  requires $$A$2[28bv32] == 0bv32;
  requires $$A$1[29bv32] == 0bv32;
  requires $$A$2[29bv32] == 0bv32;
  requires $$A$1[30bv32] == 0bv32;
  requires $$A$2[30bv32] == 0bv32;
  requires $$A$1[31bv32] == 0bv32;
  requires $$A$2[31bv32] == 0bv32;
  requires $$A$1[32bv32] == 0bv32;
  requires $$A$2[32bv32] == 0bv32;
  requires $$A$1[33bv32] == 0bv32;
  requires $$A$2[33bv32] == 0bv32;
  requires $$A$1[34bv32] == 0bv32;
  requires $$A$2[34bv32] == 0bv32;
  requires $$A$1[35bv32] == 0bv32;
  requires $$A$2[35bv32] == 0bv32;
  requires $$A$1[36bv32] == 0bv32;
  requires $$A$2[36bv32] == 0bv32;
  requires $$A$1[37bv32] == 0bv32;
  requires $$A$2[37bv32] == 0bv32;
  requires $$A$1[38bv32] == 0bv32;
  requires $$A$2[38bv32] == 0bv32;
  requires $$A$1[39bv32] == 0bv32;
  requires $$A$2[39bv32] == 0bv32;
  requires $$A$1[40bv32] == 0bv32;
  requires $$A$2[40bv32] == 0bv32;
  requires $$A$1[41bv32] == 0bv32;
  requires $$A$2[41bv32] == 0bv32;
  requires $$A$1[42bv32] == 0bv32;
  requires $$A$2[42bv32] == 0bv32;
  requires $$A$1[43bv32] == 0bv32;
  requires $$A$2[43bv32] == 0bv32;
  requires $$A$1[44bv32] == 0bv32;
  requires $$A$2[44bv32] == 0bv32;
  requires $$A$1[45bv32] == 0bv32;
  requires $$A$2[45bv32] == 0bv32;
  requires $$A$1[46bv32] == 0bv32;
  requires $$A$2[46bv32] == 0bv32;
  requires $$A$1[47bv32] == 0bv32;
  requires $$A$2[47bv32] == 0bv32;
  requires $$A$1[48bv32] == 0bv32;
  requires $$A$2[48bv32] == 0bv32;
  requires $$A$1[49bv32] == 0bv32;
  requires $$A$2[49bv32] == 0bv32;
  requires $$A$1[50bv32] == 0bv32;
  requires $$A$2[50bv32] == 0bv32;
  requires $$A$1[51bv32] == 0bv32;
  requires $$A$2[51bv32] == 0bv32;
  requires $$A$1[52bv32] == 0bv32;
  requires $$A$2[52bv32] == 0bv32;
  requires $$A$1[53bv32] == 0bv32;
  requires $$A$2[53bv32] == 0bv32;
  requires $$A$1[54bv32] == 0bv32;
  requires $$A$2[54bv32] == 0bv32;
  requires $$A$1[55bv32] == 0bv32;
  requires $$A$2[55bv32] == 0bv32;
  requires $$A$1[56bv32] == 0bv32;
  requires $$A$2[56bv32] == 0bv32;
  requires $$A$1[57bv32] == 0bv32;
  requires $$A$2[57bv32] == 0bv32;
  requires $$A$1[58bv32] == 0bv32;
  requires $$A$2[58bv32] == 0bv32;
  requires $$A$1[59bv32] == 0bv32;
  requires $$A$2[59bv32] == 0bv32;
  requires $$A$1[60bv32] == 0bv32;
  requires $$A$2[60bv32] == 0bv32;
  requires $$A$1[61bv32] == 0bv32;
  requires $$A$2[61bv32] == 0bv32;
  requires $$A$1[62bv32] == 0bv32;
  requires $$A$2[62bv32] == 0bv32;
  requires $$A$1[63bv32] == 0bv32;
  requires $$A$2[63bv32] == 0bv32;
  requires !_READ_HAS_OCCURRED_$$p && !_WRITE_HAS_OCCURRED_$$p && !_ATOMIC_HAS_OCCURRED_$$p;
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
  modifies _WRITE_HAS_OCCURRED_$$p, _WRITE_READ_BENIGN_FLAG_$$p, _WRITE_READ_BENIGN_FLAG_$$p;

implementation {:source_name "globalarray"} ULTIMATE.start()
{
  var v0$1: bv32;
  var v0$2: bv32;
  var v1$1: bool;
  var v1$2: bool;
  var p0$1: bool;
  var p0$2: bool;
  var p1$1: bool;
  var p1$2: bool;

  $entry:
    v0$1 := $$A$1[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)];
    v0$2 := $$A$2[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)];
    v1$1 := v0$1 != 0bv32;
    v1$2 := v0$2 != 0bv32;
    p0$1 := false;
    p0$2 := false;
    p1$1 := false;
    p1$2 := false;
    p0$1 := (if v1$1 then v1$1 else p0$1);
    p0$2 := (if v1$2 then v1$2 else p0$2);
    call _LOG_WRITE_$$p(p0$1, 0bv32, UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)), $$p[0bv32]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$p(p0$2, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 3} true;
    call _CHECK_WRITE_$$p(p0$2, 0bv32, UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$p"} true;
    $$p[0bv32] := (if p0$1 then UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)) else $$p[0bv32]);
    $$p[0bv32] := (if p0$2 then UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)) else $$p[0bv32]);
    return;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 8bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 8bv32 then 1bv1 else 0bv1) != 0bv1;

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

const _WATCHED_VALUE_$$p: bv32;

procedure {:inline 1} _LOG_READ_$$p(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$p;

implementation {:inline 1} _LOG_READ_$$p(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then true else _READ_HAS_OCCURRED_$$p);
    return;
}

procedure _CHECK_READ_$$p(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$p);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$p: bool;

procedure {:inline 1} _LOG_WRITE_$$p(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$p, _WRITE_READ_BENIGN_FLAG_$$p;

implementation {:inline 1} _LOG_WRITE_$$p(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then true else _WRITE_HAS_OCCURRED_$$p);
    _WRITE_READ_BENIGN_FLAG_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$p);
    return;
}

procedure _CHECK_WRITE_$$p(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$p(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$p;

implementation {:inline 1} _LOG_ATOMIC_$$p(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$p);
    return;
}

procedure _CHECK_ATOMIC_$$p(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$p;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$p := (if _P && _WRITE_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$p);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
