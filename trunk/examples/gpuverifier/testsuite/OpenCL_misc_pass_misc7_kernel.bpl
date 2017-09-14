//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP64(x: [bv32]bv64, y: bv32) returns (z$1: bv64, A$1: [bv32]bv64, z$2: bv64, A$2: [bv32]bv64);

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "in1"} {:global} $$in1: [bv32]bv64;

axiom {:array_info "$$in1"} {:global} {:elem_width 64} {:source_name "in1"} {:source_elem_width 64} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 64} {:source_elem_width 64} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$in1: bool;

var {:race_checking} {:global} {:elem_width 64} {:source_elem_width 64} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$in1: bool;

var {:race_checking} {:global} {:elem_width 64} {:source_elem_width 64} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$in1: bool;

var {:source_name "out1"} {:global} $$out1: [bv32]bv32;

axiom {:array_info "$$out1"} {:global} {:elem_width 32} {:source_name "out1"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$out1: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$out1: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$out1: bool;

var {:source_name "in2"} {:global} $$in2: [bv32]bv32;

axiom {:array_info "$$in2"} {:global} {:elem_width 32} {:source_name "in2"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$in2: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$in2: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$in2: bool;

var {:source_name "out2"} {:global} $$out2: [bv32]bv32;

axiom {:array_info "$$out2"} {:global} {:elem_width 32} {:source_name "out2"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$out2: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$out2: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$out2: bool;

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

function FEQ32(bv32, bv32) : bool;

function FEQ64(bv64, bv64) : bool;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

procedure {:source_name "float_const"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$in1 && !_WRITE_HAS_OCCURRED_$$in1 && !_ATOMIC_HAS_OCCURRED_$$in1;
  requires !_READ_HAS_OCCURRED_$$out1 && !_WRITE_HAS_OCCURRED_$$out1 && !_ATOMIC_HAS_OCCURRED_$$out1;
  requires !_READ_HAS_OCCURRED_$$in2 && !_WRITE_HAS_OCCURRED_$$in2 && !_ATOMIC_HAS_OCCURRED_$$in2;
  requires !_READ_HAS_OCCURRED_$$out2 && !_WRITE_HAS_OCCURRED_$$out2 && !_ATOMIC_HAS_OCCURRED_$$out2;
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
  modifies _WRITE_HAS_OCCURRED_$$out1, _WRITE_READ_BENIGN_FLAG_$$out1, _WRITE_READ_BENIGN_FLAG_$$out1, _WRITE_HAS_OCCURRED_$$out2, _WRITE_READ_BENIGN_FLAG_$$out2, _WRITE_READ_BENIGN_FLAG_$$out2;

implementation {:source_name "float_const"} ULTIMATE.start()
{
  var v0$1: bv64;
  var v0$2: bv64;
  var v1$1: bool;
  var v1$2: bool;
  var v2$1: bv64;
  var v2$2: bv64;
  var v3$1: bool;
  var v3$2: bool;
  var v4$1: bv32;
  var v4$2: bv32;
  var v5$1: bool;
  var v5$2: bool;
  var v6$1: bv32;
  var v6$2: bv32;
  var v7$1: bool;
  var v7$2: bool;
  var p0$1: bool;
  var p0$2: bool;
  var p1$1: bool;
  var p1$2: bool;
  var p2$1: bool;
  var p2$2: bool;
  var p3$1: bool;
  var p3$2: bool;
  var p4$1: bool;
  var p4$2: bool;
  var p5$1: bool;
  var p5$2: bool;
  var p6$1: bool;
  var p6$2: bool;
  var p7$1: bool;
  var p7$2: bool;

  $entry:
    v0$1 := $$in1[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)];
    v0$2 := $$in1[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)];
    v1$1 := FEQ64(v0$1, 9221120237041090560bv64);
    v1$2 := FEQ64(v0$2, 9221120237041090560bv64);
    p0$1 := false;
    p0$2 := false;
    p1$1 := false;
    p1$2 := false;
    p2$1 := false;
    p2$2 := false;
    p3$1 := false;
    p3$2 := false;
    p4$1 := false;
    p4$2 := false;
    p5$1 := false;
    p5$2 := false;
    p6$1 := false;
    p6$2 := false;
    p7$1 := false;
    p7$2 := false;
    p0$1 := (if v1$1 then v1$1 else p0$1);
    p0$2 := (if v1$2 then v1$2 else p0$2);
    p1$1 := (if !v1$1 then !v1$1 else p1$1);
    p1$2 := (if !v1$2 then !v1$2 else p1$2);
    call _LOG_WRITE_$$out1(p0$1, BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4294967295bv32, $$out1[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out1(p0$2, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    assume {:do_not_predicate} {:check_id "check_state_5"} {:captureState "check_state_5"} {:sourceloc} {:sourceloc_num 3} true;
    call _CHECK_WRITE_$$out1(p0$2, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4294967295bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out1"} true;
    $$out1[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)] := (if p0$1 then 4294967295bv32 else $$out1[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    $$out1[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)] := (if p0$2 then 4294967295bv32 else $$out1[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)]);
    v2$1 := (if p1$1 then $$in1[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)] else v2$1);
    v2$2 := (if p1$2 then $$in1[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)] else v2$2);
    v3$1 := (if p1$1 then FEQ64(v2$1, 9218868437227405312bv64) else v3$1);
    v3$2 := (if p1$2 then FEQ64(v2$2, 9218868437227405312bv64) else v3$2);
    p2$1 := (if p1$1 && v3$1 then v3$1 else p2$1);
    p2$2 := (if p1$2 && v3$2 then v3$2 else p2$2);
    p3$1 := (if p1$1 && !v3$1 then !v3$1 else p3$1);
    p3$2 := (if p1$2 && !v3$2 then !v3$2 else p3$2);
    call _LOG_WRITE_$$out1(p2$1, BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32, $$out1[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out1(p2$2, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    assume {:do_not_predicate} {:check_id "check_state_4"} {:captureState "check_state_4"} {:sourceloc} {:sourceloc_num 7} true;
    call _CHECK_WRITE_$$out1(p2$2, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out1"} true;
    $$out1[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)] := (if p2$1 then 1bv32 else $$out1[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    $$out1[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)] := (if p2$2 then 1bv32 else $$out1[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)]);
    call _LOG_WRITE_$$out1(p3$1, BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 0bv32, $$out1[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out1(p3$2, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 9} true;
    call _CHECK_WRITE_$$out1(p3$2, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out1"} true;
    $$out1[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)] := (if p3$1 then 0bv32 else $$out1[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    $$out1[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)] := (if p3$2 then 0bv32 else $$out1[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)]);
    v4$1 := $$in2[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)];
    v4$2 := $$in2[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)];
    v5$1 := FEQ32(v4$1, 2143289344bv32);
    v5$2 := FEQ32(v4$2, 2143289344bv32);
    p4$1 := (if v5$1 then v5$1 else p4$1);
    p4$2 := (if v5$2 then v5$2 else p4$2);
    p5$1 := (if !v5$1 then !v5$1 else p5$1);
    p5$2 := (if !v5$2 then !v5$2 else p5$2);
    call _LOG_WRITE_$$out2(p4$1, BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4294967295bv32, $$out2[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out2(p4$2, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 13} true;
    call _CHECK_WRITE_$$out2(p4$2, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4294967295bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out2"} true;
    $$out2[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)] := (if p4$1 then 4294967295bv32 else $$out2[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    $$out2[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)] := (if p4$2 then 4294967295bv32 else $$out2[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)]);
    v6$1 := (if p5$1 then $$in2[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)] else v6$1);
    v6$2 := (if p5$2 then $$in2[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)] else v6$2);
    v7$1 := (if p5$1 then FEQ32(v6$1, 2139095040bv32) else v7$1);
    v7$2 := (if p5$2 then FEQ32(v6$2, 2139095040bv32) else v7$2);
    p6$1 := (if p5$1 && v7$1 then v7$1 else p6$1);
    p6$2 := (if p5$2 && v7$2 then v7$2 else p6$2);
    p7$1 := (if p5$1 && !v7$1 then !v7$1 else p7$1);
    p7$2 := (if p5$2 && !v7$2 then !v7$2 else p7$2);
    call _LOG_WRITE_$$out2(p6$1, BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32, $$out2[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out2(p6$2, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 17} true;
    call _CHECK_WRITE_$$out2(p6$2, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out2"} true;
    $$out2[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)] := (if p6$1 then 1bv32 else $$out2[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    $$out2[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)] := (if p6$2 then 1bv32 else $$out2[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)]);
    call _LOG_WRITE_$$out2(p7$1, BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 0bv32, $$out2[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$out2(p7$2, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 19} true;
    call _CHECK_WRITE_$$out2(p7$2, BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$out2"} true;
    $$out2[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)] := (if p7$1 then 0bv32 else $$out2[BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)]);
    $$out2[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)] := (if p7$2 then 0bv32 else $$out2[BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)]);
    return;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 1024bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 1024bv32 then 1bv1 else 0bv1) != 0bv1;

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

const _WATCHED_VALUE_$$in1: bv64;

procedure {:inline 1} _LOG_READ_$$in1(_P: bool, _offset: bv32, _value: bv64);
  modifies _READ_HAS_OCCURRED_$$in1;

implementation {:inline 1} _LOG_READ_$$in1(_P: bool, _offset: bv32, _value: bv64)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$in1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$in1 == _value then true else _READ_HAS_OCCURRED_$$in1);
    return;
}

procedure _CHECK_READ_$$in1(_P: bool, _offset: bv32, _value: bv64);
  requires !(_P && _WRITE_HAS_OCCURRED_$$in1 && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$in1);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$in1 && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$in1: bool;

procedure {:inline 1} _LOG_WRITE_$$in1(_P: bool, _offset: bv32, _value: bv64, _value_old: bv64);
  modifies _WRITE_HAS_OCCURRED_$$in1, _WRITE_READ_BENIGN_FLAG_$$in1;

implementation {:inline 1} _LOG_WRITE_$$in1(_P: bool, _offset: bv32, _value: bv64, _value_old: bv64)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$in1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$in1 == _value then true else _WRITE_HAS_OCCURRED_$$in1);
    _WRITE_READ_BENIGN_FLAG_$$in1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$in1 == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$in1);
    return;
}

procedure _CHECK_WRITE_$$in1(_P: bool, _offset: bv32, _value: bv64);
  requires !(_P && _WRITE_HAS_OCCURRED_$$in1 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$in1 != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$in1 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$in1 != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$in1 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$in1(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$in1;

implementation {:inline 1} _LOG_ATOMIC_$$in1(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$in1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$in1);
    return;
}

procedure _CHECK_ATOMIC_$$in1(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$in1 && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$in1 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$in1(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$in1;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$in1(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$in1 := (if _P && _WRITE_HAS_OCCURRED_$$in1 && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$in1);
    return;
}

const _WATCHED_VALUE_$$out1: bv32;

procedure {:inline 1} _LOG_READ_$$out1(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$out1;

implementation {:inline 1} _LOG_READ_$$out1(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$out1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$out1 == _value then true else _READ_HAS_OCCURRED_$$out1);
    return;
}

procedure _CHECK_READ_$$out1(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$out1 && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$out1);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$out1 && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$out1: bool;

procedure {:inline 1} _LOG_WRITE_$$out1(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$out1, _WRITE_READ_BENIGN_FLAG_$$out1;

implementation {:inline 1} _LOG_WRITE_$$out1(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$out1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$out1 == _value then true else _WRITE_HAS_OCCURRED_$$out1);
    _WRITE_READ_BENIGN_FLAG_$$out1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$out1 == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$out1);
    return;
}

procedure _CHECK_WRITE_$$out1(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$out1 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$out1 != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$out1 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$out1 != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$out1 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$out1(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$out1;

implementation {:inline 1} _LOG_ATOMIC_$$out1(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$out1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$out1);
    return;
}

procedure _CHECK_ATOMIC_$$out1(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$out1 && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$out1 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$out1(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$out1;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$out1(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$out1 := (if _P && _WRITE_HAS_OCCURRED_$$out1 && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$out1);
    return;
}

const _WATCHED_VALUE_$$in2: bv32;

procedure {:inline 1} _LOG_READ_$$in2(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$in2;

implementation {:inline 1} _LOG_READ_$$in2(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$in2 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$in2 == _value then true else _READ_HAS_OCCURRED_$$in2);
    return;
}

procedure _CHECK_READ_$$in2(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$in2 && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$in2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$in2 && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$in2: bool;

procedure {:inline 1} _LOG_WRITE_$$in2(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$in2, _WRITE_READ_BENIGN_FLAG_$$in2;

implementation {:inline 1} _LOG_WRITE_$$in2(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$in2 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$in2 == _value then true else _WRITE_HAS_OCCURRED_$$in2);
    _WRITE_READ_BENIGN_FLAG_$$in2 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$in2 == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$in2);
    return;
}

procedure _CHECK_WRITE_$$in2(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$in2 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$in2 != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$in2 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$in2 != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$in2 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$in2(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$in2;

implementation {:inline 1} _LOG_ATOMIC_$$in2(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$in2 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$in2);
    return;
}

procedure _CHECK_ATOMIC_$$in2(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$in2 && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$in2 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$in2(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$in2;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$in2(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$in2 := (if _P && _WRITE_HAS_OCCURRED_$$in2 && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$in2);
    return;
}

const _WATCHED_VALUE_$$out2: bv32;

procedure {:inline 1} _LOG_READ_$$out2(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$out2;

implementation {:inline 1} _LOG_READ_$$out2(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$out2 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$out2 == _value then true else _READ_HAS_OCCURRED_$$out2);
    return;
}

procedure _CHECK_READ_$$out2(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$out2 && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$out2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$out2 && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$out2: bool;

procedure {:inline 1} _LOG_WRITE_$$out2(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$out2, _WRITE_READ_BENIGN_FLAG_$$out2;

implementation {:inline 1} _LOG_WRITE_$$out2(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$out2 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$out2 == _value then true else _WRITE_HAS_OCCURRED_$$out2);
    _WRITE_READ_BENIGN_FLAG_$$out2 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$out2 == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$out2);
    return;
}

procedure _CHECK_WRITE_$$out2(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$out2 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$out2 != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$out2 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$out2 != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$out2 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$out2(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$out2;

implementation {:inline 1} _LOG_ATOMIC_$$out2(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$out2 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$out2);
    return;
}

procedure _CHECK_ATOMIC_$$out2(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$out2 && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$out2 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$out2(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$out2;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$out2(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$out2 := (if _P && _WRITE_HAS_OCCURRED_$$out2 && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$out2);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
