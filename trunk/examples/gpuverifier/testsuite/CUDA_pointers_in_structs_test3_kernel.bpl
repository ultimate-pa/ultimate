//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP8(x: [bv32]bv8, y: bv32) returns (z$1: bv8, A$1: [bv32]bv8, z$2: bv8, A$2: [bv32]bv8);

var {:source_name "A.coerce0.coerce0"} {:global} $$A.coerce0.coerce0: [bv32]bv8;

axiom {:array_info "$$A.coerce0.coerce0"} {:global} {:elem_width 8} {:source_name "A.coerce0.coerce0"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$A.coerce0.coerce0: bool;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$A.coerce0.coerce0: bool;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$A.coerce0.coerce0: bool;

const $arrayId$$A.coerce0.coerce0: arrayId;

axiom $arrayId$$A.coerce0.coerce0 == 1bv2;

var {:source_name "A.val"} $$A.val$1: [bv32]bv8;

var {:source_name "A.val"} $$A.val$2: [bv32]bv8;

axiom {:array_info "$$A.val"} {:elem_width 8} {:source_name "A.val"} {:source_elem_width 32} {:source_dimensions "1"} true;

const $arrayId$$A.val: arrayId;

axiom $arrayId$$A.val == 2bv2;

type ptr = bv32;

type arrayId = bv2;

function {:inline true} MKPTR(base: arrayId, offset: bv32) : ptr
{
  base ++ offset[30:0]
}

function {:inline true} base#MKPTR(p: ptr) : arrayId
{
  p[32:30]
}

function {:inline true} offset#MKPTR(p: ptr) : bv32
{
  0bv2 ++ p[30:0]
}

const $arrayId$$null$: arrayId;

axiom $arrayId$$null$ == 0bv2;

const _WATCHED_OFFSET: bv32;

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

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

procedure {:source_name "foo"} ULTIMATE.start($A: bv32);
  requires $A == MKPTR($arrayId$$A.coerce0.coerce0, 0bv32);
  requires !_READ_HAS_OCCURRED_$$A.coerce0.coerce0 && !_WRITE_HAS_OCCURRED_$$A.coerce0.coerce0 && !_ATOMIC_HAS_OCCURRED_$$A.coerce0.coerce0;
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
  modifies _WRITE_HAS_OCCURRED_$$A.coerce0.coerce0, _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0, _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0;

implementation {:source_name "foo"} ULTIMATE.start($A: bv32)
{
  var v1$1: bv8;
  var v1$2: bv8;
  var v0$1: bv8;
  var v0$2: bv8;
  var v2$1: bv8;
  var v2$2: bv8;
  var v3$1: bv8;
  var v3$2: bv8;
  var v4$1: ptr;
  var v4$2: ptr;
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
  var p8$1: bool;
  var p8$2: bool;
  var p9$1: bool;
  var p9$2: bool;
  var p10$1: bool;
  var p10$2: bool;
  var p11$1: bool;
  var p11$2: bool;
  var p12$1: bool;
  var p12$2: bool;
  var p13$1: bool;
  var p13$2: bool;
  var p14$1: bool;
  var p14$2: bool;
  var p15$1: bool;
  var p15$2: bool;

  $entry:
    $$A.val$1[0bv32] := $A[8:0];
    $$A.val$2[0bv32] := $A[8:0];
    $$A.val$1[1bv32] := $A[16:8];
    $$A.val$2[1bv32] := $A[16:8];
    $$A.val$1[2bv32] := $A[24:16];
    $$A.val$2[2bv32] := $A[24:16];
    $$A.val$1[3bv32] := $A[32:24];
    $$A.val$2[3bv32] := $A[32:24];
    v0$1 := $$A.val$1[0bv32];
    v0$2 := $$A.val$2[0bv32];
    v1$1 := $$A.val$1[1bv32];
    v1$2 := $$A.val$2[1bv32];
    v2$1 := $$A.val$1[2bv32];
    v2$2 := $$A.val$2[2bv32];
    v3$1 := $$A.val$1[3bv32];
    v3$2 := $$A.val$2[3bv32];
    v4$1 := v3$1 ++ v2$1 ++ v1$1 ++ v0$1;
    v4$2 := v3$2 ++ v2$2 ++ v1$2 ++ v0$2;
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
    p8$1 := false;
    p8$2 := false;
    p9$1 := false;
    p9$2 := false;
    p10$1 := false;
    p10$2 := false;
    p11$1 := false;
    p11$2 := false;
    p12$1 := false;
    p12$2 := false;
    p13$1 := false;
    p13$2 := false;
    p14$1 := false;
    p14$2 := false;
    p15$1 := false;
    p15$2 := false;
    p0$1 := (if base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce0 else p0$1);
    p0$2 := (if base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce0 else p0$2);
    p1$1 := (if base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce0 else p1$1);
    p1$2 := (if base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce0 else p1$2);
    call _LOG_WRITE_$$A.coerce0.coerce0(p0$1, BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), local_id_x$1[8:0], $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0(p0$2, BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)));
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 5} true;
    call _CHECK_WRITE_$$A.coerce0.coerce0(p0$2, BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), local_id_x$2[8:0]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce0"} true;
    $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))] := (if p0$1 then local_id_x$1[8:0] else $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))]);
    $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))] := (if p0$2 then local_id_x$2[8:0] else $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))]);
    p2$1 := (if p1$1 && base#MKPTR(v4$1) == $arrayId$$A.val then base#MKPTR(v4$1) == $arrayId$$A.val else p2$1);
    p2$2 := (if p1$2 && base#MKPTR(v4$2) == $arrayId$$A.val then base#MKPTR(v4$2) == $arrayId$$A.val else p2$2);
    p3$1 := (if p1$1 && base#MKPTR(v4$1) != $arrayId$$A.val then base#MKPTR(v4$1) != $arrayId$$A.val else p3$1);
    p3$2 := (if p1$2 && base#MKPTR(v4$2) != $arrayId$$A.val then base#MKPTR(v4$2) != $arrayId$$A.val else p3$2);
    $$A.val$1[BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))] := (if p2$1 then local_id_x$1[8:0] else $$A.val$1[BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))]);
    $$A.val$2[BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))] := (if p2$2 then local_id_x$2[8:0] else $$A.val$2[BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))]);
    assert {:bad_pointer_access} {:sourceloc_num 7} {:thread 1} p3$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 7} {:thread 2} p3$2 ==> false;
    p4$1 := (if base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce0 else p4$1);
    p4$2 := (if base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce0 else p4$2);
    p5$1 := (if base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce0 else p5$1);
    p5$2 := (if base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce0 else p5$2);
    call _LOG_WRITE_$$A.coerce0.coerce0(p4$1, BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32), local_id_x$1[16:8], $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0(p4$2, BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 8} true;
    call _CHECK_WRITE_$$A.coerce0.coerce0(p4$2, BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32), local_id_x$2[16:8]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce0"} true;
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)] := (if p4$1 then local_id_x$1[16:8] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)]);
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)] := (if p4$2 then local_id_x$2[16:8] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)]);
    p6$1 := (if p5$1 && base#MKPTR(v4$1) == $arrayId$$A.val then base#MKPTR(v4$1) == $arrayId$$A.val else p6$1);
    p6$2 := (if p5$2 && base#MKPTR(v4$2) == $arrayId$$A.val then base#MKPTR(v4$2) == $arrayId$$A.val else p6$2);
    p7$1 := (if p5$1 && base#MKPTR(v4$1) != $arrayId$$A.val then base#MKPTR(v4$1) != $arrayId$$A.val else p7$1);
    p7$2 := (if p5$2 && base#MKPTR(v4$2) != $arrayId$$A.val then base#MKPTR(v4$2) != $arrayId$$A.val else p7$2);
    $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)] := (if p6$1 then local_id_x$1[16:8] else $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)]);
    $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)] := (if p6$2 then local_id_x$2[16:8] else $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)]);
    assert {:bad_pointer_access} {:sourceloc_num 10} {:thread 1} p7$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 10} {:thread 2} p7$2 ==> false;
    p8$1 := (if base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce0 else p8$1);
    p8$2 := (if base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce0 else p8$2);
    p9$1 := (if base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce0 else p9$1);
    p9$2 := (if base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce0 else p9$2);
    call _LOG_WRITE_$$A.coerce0.coerce0(p8$1, BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32), local_id_x$1[24:16], $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0(p8$2, BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 11} true;
    call _CHECK_WRITE_$$A.coerce0.coerce0(p8$2, BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32), local_id_x$2[24:16]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce0"} true;
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)] := (if p8$1 then local_id_x$1[24:16] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)]);
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)] := (if p8$2 then local_id_x$2[24:16] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)]);
    p10$1 := (if p9$1 && base#MKPTR(v4$1) == $arrayId$$A.val then base#MKPTR(v4$1) == $arrayId$$A.val else p10$1);
    p10$2 := (if p9$2 && base#MKPTR(v4$2) == $arrayId$$A.val then base#MKPTR(v4$2) == $arrayId$$A.val else p10$2);
    p11$1 := (if p9$1 && base#MKPTR(v4$1) != $arrayId$$A.val then base#MKPTR(v4$1) != $arrayId$$A.val else p11$1);
    p11$2 := (if p9$2 && base#MKPTR(v4$2) != $arrayId$$A.val then base#MKPTR(v4$2) != $arrayId$$A.val else p11$2);
    $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)] := (if p10$1 then local_id_x$1[24:16] else $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)]);
    $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)] := (if p10$2 then local_id_x$2[24:16] else $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)]);
    assert {:bad_pointer_access} {:sourceloc_num 13} {:thread 1} p11$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 13} {:thread 2} p11$2 ==> false;
    p12$1 := (if base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce0 else p12$1);
    p12$2 := (if base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce0 else p12$2);
    p13$1 := (if base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce0 else p13$1);
    p13$2 := (if base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce0 else p13$2);
    call _LOG_WRITE_$$A.coerce0.coerce0(p12$1, BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32), local_id_x$1[32:24], $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0(p12$2, BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32));
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 14} true;
    call _CHECK_WRITE_$$A.coerce0.coerce0(p12$2, BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32), local_id_x$2[32:24]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce0"} true;
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)] := (if p12$1 then local_id_x$1[32:24] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)]);
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)] := (if p12$2 then local_id_x$2[32:24] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)]);
    p14$1 := (if p13$1 && base#MKPTR(v4$1) == $arrayId$$A.val then base#MKPTR(v4$1) == $arrayId$$A.val else p14$1);
    p14$2 := (if p13$2 && base#MKPTR(v4$2) == $arrayId$$A.val then base#MKPTR(v4$2) == $arrayId$$A.val else p14$2);
    p15$1 := (if p13$1 && base#MKPTR(v4$1) != $arrayId$$A.val then base#MKPTR(v4$1) != $arrayId$$A.val else p15$1);
    p15$2 := (if p13$2 && base#MKPTR(v4$2) != $arrayId$$A.val then base#MKPTR(v4$2) != $arrayId$$A.val else p15$2);
    $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)] := (if p14$1 then local_id_x$1[32:24] else $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)]);
    $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)] := (if p14$2 then local_id_x$2[32:24] else $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)]);
    assert {:bad_pointer_access} {:sourceloc_num 16} {:thread 1} p15$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 16} {:thread 2} p15$2 ==> false;
    return;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 2bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 2bv32 then 1bv1 else 0bv1) != 0bv1;

const {:local_id_y} local_id_y$1: bv32;

const {:local_id_y} local_id_y$2: bv32;

const {:local_id_z} local_id_z$1: bv32;

const {:local_id_z} local_id_z$2: bv32;

const {:group_id_y} group_id_y$1: bv32;

const {:group_id_y} group_id_y$2: bv32;

const {:group_id_z} group_id_z$1: bv32;

const {:group_id_z} group_id_z$2: bv32;

const _WATCHED_VALUE_$$A.coerce0.coerce0: bv8;

procedure {:inline 1} _LOG_READ_$$A.coerce0.coerce0(_P: bool, _offset: bv32, _value: bv8);
  modifies _READ_HAS_OCCURRED_$$A.coerce0.coerce0;

implementation {:inline 1} _LOG_READ_$$A.coerce0.coerce0(_P: bool, _offset: bv32, _value: bv8)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$A.coerce0.coerce0 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A.coerce0.coerce0 == _value then true else _READ_HAS_OCCURRED_$$A.coerce0.coerce0);
    return;
}

procedure _CHECK_READ_$$A.coerce0.coerce0(_P: bool, _offset: bv32, _value: bv8);
  requires !(_P && _WRITE_HAS_OCCURRED_$$A.coerce0.coerce0 && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$A.coerce0.coerce0 && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0: bool;

procedure {:inline 1} _LOG_WRITE_$$A.coerce0.coerce0(_P: bool, _offset: bv32, _value: bv8, _value_old: bv8);
  modifies _WRITE_HAS_OCCURRED_$$A.coerce0.coerce0, _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0;

implementation {:inline 1} _LOG_WRITE_$$A.coerce0.coerce0(_P: bool, _offset: bv32, _value: bv8, _value_old: bv8)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$A.coerce0.coerce0 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A.coerce0.coerce0 == _value then true else _WRITE_HAS_OCCURRED_$$A.coerce0.coerce0);
    _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A.coerce0.coerce0 == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0);
    return;
}

procedure _CHECK_WRITE_$$A.coerce0.coerce0(_P: bool, _offset: bv32, _value: bv8);
  requires !(_P && _WRITE_HAS_OCCURRED_$$A.coerce0.coerce0 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A.coerce0.coerce0 != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$A.coerce0.coerce0 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A.coerce0.coerce0 != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$A.coerce0.coerce0 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$A.coerce0.coerce0(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$A.coerce0.coerce0;

implementation {:inline 1} _LOG_ATOMIC_$$A.coerce0.coerce0(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$A.coerce0.coerce0 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$A.coerce0.coerce0);
    return;
}

procedure _CHECK_ATOMIC_$$A.coerce0.coerce0(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$A.coerce0.coerce0 && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$A.coerce0.coerce0 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0 := (if _P && _WRITE_HAS_OCCURRED_$$A.coerce0.coerce0 && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
