//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP8(x: [bv32]bv8, y: bv32) returns (z$1: bv8, A$1: [bv32]bv8, z$2: bv8, A$2: [bv32]bv8);

var {:source_name "A"} {:global} $$A: [bv32]bv8;

axiom {:array_info "$$A"} {:global} {:elem_width 8} {:source_name "A"} {:source_elem_width 8} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 8} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$A: bool;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 8} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$A: bool;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 8} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$A: bool;

const $arrayId$$A: arrayId;

axiom $arrayId$$A == 1bv3;

var {:source_name "B"} {:global} $$B: [bv32]bv8;

axiom {:array_info "$$B"} {:global} {:elem_width 8} {:source_name "B"} {:source_elem_width 8} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 8} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$B: bool;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 8} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$B: bool;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 8} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$B: bool;

const $arrayId$$B: arrayId;

axiom $arrayId$$B == 2bv3;

var {:source_name "choice1"} $$choice1$1: [bv32]bv8;

var {:source_name "choice1"} $$choice1$2: [bv32]bv8;

axiom {:array_info "$$choice1"} {:elem_width 8} {:source_name "choice1"} {:source_elem_width 32} {:source_dimensions "1"} true;

const $arrayId$$choice1: arrayId;

axiom $arrayId$$choice1 == 3bv3;

var {:source_name "choice2"} $$choice2$1: [bv32]bv8;

var {:source_name "choice2"} $$choice2$2: [bv32]bv8;

axiom {:array_info "$$choice2"} {:elem_width 8} {:source_name "choice2"} {:source_elem_width 32} {:source_dimensions "1"} true;

const $arrayId$$choice2: arrayId;

axiom $arrayId$$choice2 == 4bv3;

type ptr = bv32;

type arrayId = bv3;

function {:inline true} MKPTR(base: arrayId, offset: bv32) : ptr
{
  base ++ offset[29:0]
}

function {:inline true} base#MKPTR(p: ptr) : arrayId
{
  p[32:29]
}

function {:inline true} offset#MKPTR(p: ptr) : bv32
{
  0bv3 ++ p[29:0]
}

const $arrayId$$null$: arrayId;

axiom $arrayId$$null$ == 0bv3;

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

procedure {:source_name "foo"} ULTIMATE.start($c: bv8);
  requires !_READ_HAS_OCCURRED_$$A && !_WRITE_HAS_OCCURRED_$$A && !_ATOMIC_HAS_OCCURRED_$$A;
  requires !_READ_HAS_OCCURRED_$$B && !_WRITE_HAS_OCCURRED_$$B && !_ATOMIC_HAS_OCCURRED_$$B;
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
  modifies _READ_HAS_OCCURRED_$$B, _READ_HAS_OCCURRED_$$A, _WRITE_HAS_OCCURRED_$$B, _WRITE_READ_BENIGN_FLAG_$$B, _WRITE_READ_BENIGN_FLAG_$$B, _WRITE_HAS_OCCURRED_$$A, _WRITE_READ_BENIGN_FLAG_$$A, _WRITE_READ_BENIGN_FLAG_$$A;

implementation {:source_name "foo"} ULTIMATE.start($c: bv8)
{
  var $cond: ptr;
  var $cond5: ptr;
  var v0: bool;
  var v1: bv32;
  var v2: bool;
  var v3: bv32;
  var v4$1: bv8;
  var v4$2: bv8;
  var v5$1: bv8;
  var v5$2: bv8;
  var v6$1: bv8;
  var v6$2: bv8;
  var v7$1: bv8;
  var v7$2: bv8;
  var v8$1: ptr;
  var v8$2: ptr;
  var v10$1: bv8;
  var v10$2: bv8;
  var v9$1: bv8;
  var v9$2: bv8;
  var v11$1: bv8;
  var v11$2: bv8;
  var v12$1: bv8;
  var v12$2: bv8;
  var v13$1: bv8;
  var v13$2: bv8;
  var v14$1: ptr;
  var v14$2: ptr;
  var v15$1: bv8;
  var v15$2: bv8;
  var v16$1: bv8;
  var v16$2: bv8;
  var v17$1: bv8;
  var v17$2: bv8;
  var v18$1: bv8;
  var v18$2: bv8;
  var v19$1: bv8;
  var v19$2: bv8;
  var v22$1: bv8;
  var v22$2: bv8;
  var v23$1: ptr;
  var v23$2: ptr;
  var v20$1: bv8;
  var v20$2: bv8;
  var v21$1: bv8;
  var v21$2: bv8;
  var v25$1: bv8;
  var v25$2: bv8;
  var v24$1: bv8;
  var v24$2: bv8;
  var v26$1: bv8;
  var v26$2: bv8;
  var v27$1: bv8;
  var v27$2: bv8;
  var v28$1: bv8;
  var v28$2: bv8;
  var v29$1: ptr;
  var v29$2: ptr;
  var v30$1: bv8;
  var v30$2: bv8;
  var v31$1: bv8;
  var v31$2: bv8;
  var v32$1: bv8;
  var v32$2: bv8;
  var v33$1: bv8;
  var v33$2: bv8;
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
  var p16$1: bool;
  var p16$2: bool;
  var p17$1: bool;
  var p17$2: bool;
  var p18$1: bool;
  var p18$2: bool;
  var p19$1: bool;
  var p19$2: bool;
  var p20$1: bool;
  var p20$2: bool;
  var p21$1: bool;
  var p21$2: bool;
  var p22$1: bool;
  var p22$2: bool;
  var p23$1: bool;
  var p23$2: bool;
  var p24$1: bool;
  var p24$2: bool;
  var p25$1: bool;
  var p25$2: bool;
  var p26$1: bool;
  var p26$2: bool;
  var p27$1: bool;
  var p27$2: bool;
  var p28$1: bool;
  var p28$2: bool;
  var p29$1: bool;
  var p29$2: bool;
  var p30$1: bool;
  var p30$2: bool;
  var p31$1: bool;
  var p31$2: bool;

  $entry:
    v0 := $c != 0bv8;
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
    p16$1 := false;
    p16$2 := false;
    p17$1 := false;
    p17$2 := false;
    p18$1 := false;
    p18$2 := false;
    p19$1 := false;
    p19$2 := false;
    p20$1 := false;
    p20$2 := false;
    p21$1 := false;
    p21$2 := false;
    p22$1 := false;
    p22$2 := false;
    p23$1 := false;
    p23$2 := false;
    p24$1 := false;
    p24$2 := false;
    p25$1 := false;
    p25$2 := false;
    p26$1 := false;
    p26$2 := false;
    p27$1 := false;
    p27$2 := false;
    p28$1 := false;
    p28$2 := false;
    p29$1 := false;
    p29$2 := false;
    p30$1 := false;
    p30$2 := false;
    p31$1 := false;
    p31$2 := false;
    goto $truebb, $falsebb;

  $falsebb:
    assume {:partition} !v0;
    $cond := MKPTR($arrayId$$B, 0bv32);
    goto $cond.end;

  $cond.end:
    v1 := MKPTR(base#MKPTR($cond), offset#MKPTR($cond));
    $$choice1$1[0bv32] := v1[8:0];
    $$choice1$2[0bv32] := v1[8:0];
    $$choice1$1[1bv32] := v1[16:8];
    $$choice1$2[1bv32] := v1[16:8];
    $$choice1$1[2bv32] := v1[24:16];
    $$choice1$2[2bv32] := v1[24:16];
    $$choice1$1[3bv32] := v1[32:24];
    $$choice1$2[3bv32] := v1[32:24];
    v2 := $c != 0bv8;
    goto $truebb0, $falsebb0;

  $falsebb0:
    assume {:partition} !v2;
    $cond5 := MKPTR($arrayId$$A, 0bv32);
    goto $cond.end4;

  $cond.end4:
    v3 := MKPTR(base#MKPTR($cond5), offset#MKPTR($cond5));
    $$choice2$1[0bv32] := v3[8:0];
    $$choice2$2[0bv32] := v3[8:0];
    $$choice2$1[1bv32] := v3[16:8];
    $$choice2$2[1bv32] := v3[16:8];
    $$choice2$1[2bv32] := v3[24:16];
    $$choice2$2[2bv32] := v3[24:16];
    $$choice2$1[3bv32] := v3[32:24];
    $$choice2$2[3bv32] := v3[32:24];
    v4$1 := $$choice1$1[0bv32];
    v4$2 := $$choice1$2[0bv32];
    v5$1 := $$choice1$1[1bv32];
    v5$2 := $$choice1$2[1bv32];
    v6$1 := $$choice1$1[2bv32];
    v6$2 := $$choice1$2[2bv32];
    v7$1 := $$choice1$1[3bv32];
    v7$2 := $$choice1$2[3bv32];
    v8$1 := v7$1 ++ v6$1 ++ v5$1 ++ v4$1;
    v8$2 := v7$2 ++ v6$2 ++ v5$2 ++ v4$2;
    p0$1 := (if base#MKPTR(v8$1) == $arrayId$$B then base#MKPTR(v8$1) == $arrayId$$B else p0$1);
    p0$2 := (if base#MKPTR(v8$2) == $arrayId$$B then base#MKPTR(v8$2) == $arrayId$$B else p0$2);
    p1$1 := (if base#MKPTR(v8$1) != $arrayId$$B then base#MKPTR(v8$1) != $arrayId$$B else p1$1);
    p1$2 := (if base#MKPTR(v8$2) != $arrayId$$B then base#MKPTR(v8$2) != $arrayId$$B else p1$2);
    call _LOG_READ_$$B(p0$1, BV32_ADD(offset#MKPTR(v8$1), local_id_x$1), $$B[BV32_ADD(offset#MKPTR(v8$1), local_id_x$1)]);
    assume {:do_not_predicate} {:check_id "check_state_7"} {:captureState "check_state_7"} {:sourceloc} {:sourceloc_num 19} true;
    call _CHECK_READ_$$B(p0$2, BV32_ADD(offset#MKPTR(v8$2), local_id_x$2), $$B[BV32_ADD(offset#MKPTR(v8$2), local_id_x$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$B"} true;
    v9$1 := (if p0$1 then $$B[BV32_ADD(offset#MKPTR(v8$1), local_id_x$1)] else v9$1);
    v9$2 := (if p0$2 then $$B[BV32_ADD(offset#MKPTR(v8$2), local_id_x$2)] else v9$2);
    p2$1 := (if p1$1 && base#MKPTR(v8$1) == $arrayId$$A then base#MKPTR(v8$1) == $arrayId$$A else p2$1);
    p2$2 := (if p1$2 && base#MKPTR(v8$2) == $arrayId$$A then base#MKPTR(v8$2) == $arrayId$$A else p2$2);
    p3$1 := (if p1$1 && base#MKPTR(v8$1) != $arrayId$$A then base#MKPTR(v8$1) != $arrayId$$A else p3$1);
    p3$2 := (if p1$2 && base#MKPTR(v8$2) != $arrayId$$A then base#MKPTR(v8$2) != $arrayId$$A else p3$2);
    call _LOG_READ_$$A(p2$1, BV32_ADD(offset#MKPTR(v8$1), local_id_x$1), $$A[BV32_ADD(offset#MKPTR(v8$1), local_id_x$1)]);
    assume {:do_not_predicate} {:check_id "check_state_6"} {:captureState "check_state_6"} {:sourceloc} {:sourceloc_num 20} true;
    call _CHECK_READ_$$A(p2$2, BV32_ADD(offset#MKPTR(v8$2), local_id_x$2), $$A[BV32_ADD(offset#MKPTR(v8$2), local_id_x$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    v9$1 := (if p2$1 then $$A[BV32_ADD(offset#MKPTR(v8$1), local_id_x$1)] else v9$1);
    v9$2 := (if p2$2 then $$A[BV32_ADD(offset#MKPTR(v8$2), local_id_x$2)] else v9$2);
    p4$1 := (if p3$1 && base#MKPTR(v8$1) == $arrayId$$choice1 then base#MKPTR(v8$1) == $arrayId$$choice1 else p4$1);
    p4$2 := (if p3$2 && base#MKPTR(v8$2) == $arrayId$$choice1 then base#MKPTR(v8$2) == $arrayId$$choice1 else p4$2);
    p5$1 := (if p3$1 && base#MKPTR(v8$1) != $arrayId$$choice1 then base#MKPTR(v8$1) != $arrayId$$choice1 else p5$1);
    p5$2 := (if p3$2 && base#MKPTR(v8$2) != $arrayId$$choice1 then base#MKPTR(v8$2) != $arrayId$$choice1 else p5$2);
    v9$1 := (if p4$1 then $$choice1$1[BV32_ADD(offset#MKPTR(v8$1), local_id_x$1)] else v9$1);
    v9$2 := (if p4$2 then $$choice1$2[BV32_ADD(offset#MKPTR(v8$2), local_id_x$2)] else v9$2);
    p6$1 := (if p5$1 && base#MKPTR(v8$1) == $arrayId$$choice2 then base#MKPTR(v8$1) == $arrayId$$choice2 else p6$1);
    p6$2 := (if p5$2 && base#MKPTR(v8$2) == $arrayId$$choice2 then base#MKPTR(v8$2) == $arrayId$$choice2 else p6$2);
    p7$1 := (if p5$1 && base#MKPTR(v8$1) != $arrayId$$choice2 then base#MKPTR(v8$1) != $arrayId$$choice2 else p7$1);
    p7$2 := (if p5$2 && base#MKPTR(v8$2) != $arrayId$$choice2 then base#MKPTR(v8$2) != $arrayId$$choice2 else p7$2);
    v9$1 := (if p6$1 then $$choice2$1[BV32_ADD(offset#MKPTR(v8$1), local_id_x$1)] else v9$1);
    v9$2 := (if p6$2 then $$choice2$2[BV32_ADD(offset#MKPTR(v8$2), local_id_x$2)] else v9$2);
    assert {:bad_pointer_access} {:sourceloc_num 23} {:thread 1} p7$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 23} {:thread 2} p7$2 ==> false;
    v10$1 := $$choice2$1[0bv32];
    v10$2 := $$choice2$2[0bv32];
    v11$1 := $$choice2$1[1bv32];
    v11$2 := $$choice2$2[1bv32];
    v12$1 := $$choice2$1[2bv32];
    v12$2 := $$choice2$2[2bv32];
    v13$1 := $$choice2$1[3bv32];
    v13$2 := $$choice2$2[3bv32];
    v14$1 := v13$1 ++ v12$1 ++ v11$1 ++ v10$1;
    v14$2 := v13$2 ++ v12$2 ++ v11$2 ++ v10$2;
    p8$1 := (if base#MKPTR(v14$1) == $arrayId$$B then base#MKPTR(v14$1) == $arrayId$$B else p8$1);
    p8$2 := (if base#MKPTR(v14$2) == $arrayId$$B then base#MKPTR(v14$2) == $arrayId$$B else p8$2);
    p9$1 := (if base#MKPTR(v14$1) != $arrayId$$B then base#MKPTR(v14$1) != $arrayId$$B else p9$1);
    p9$2 := (if base#MKPTR(v14$2) != $arrayId$$B then base#MKPTR(v14$2) != $arrayId$$B else p9$2);
    call _LOG_WRITE_$$B(p8$1, BV32_ADD(offset#MKPTR(v14$1), local_id_x$1), v9$1, $$B[BV32_ADD(offset#MKPTR(v14$1), local_id_x$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$B(p8$2, BV32_ADD(offset#MKPTR(v14$2), local_id_x$2));
    assume {:do_not_predicate} {:check_id "check_state_5"} {:captureState "check_state_5"} {:sourceloc} {:sourceloc_num 28} true;
    call _CHECK_WRITE_$$B(p8$2, BV32_ADD(offset#MKPTR(v14$2), local_id_x$2), v9$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$B"} true;
    $$B[BV32_ADD(offset#MKPTR(v14$1), local_id_x$1)] := (if p8$1 then v9$1 else $$B[BV32_ADD(offset#MKPTR(v14$1), local_id_x$1)]);
    $$B[BV32_ADD(offset#MKPTR(v14$2), local_id_x$2)] := (if p8$2 then v9$2 else $$B[BV32_ADD(offset#MKPTR(v14$2), local_id_x$2)]);
    p10$1 := (if p9$1 && base#MKPTR(v14$1) == $arrayId$$A then base#MKPTR(v14$1) == $arrayId$$A else p10$1);
    p10$2 := (if p9$2 && base#MKPTR(v14$2) == $arrayId$$A then base#MKPTR(v14$2) == $arrayId$$A else p10$2);
    p11$1 := (if p9$1 && base#MKPTR(v14$1) != $arrayId$$A then base#MKPTR(v14$1) != $arrayId$$A else p11$1);
    p11$2 := (if p9$2 && base#MKPTR(v14$2) != $arrayId$$A then base#MKPTR(v14$2) != $arrayId$$A else p11$2);
    call _LOG_WRITE_$$A(p10$1, BV32_ADD(offset#MKPTR(v14$1), local_id_x$1), v9$1, $$A[BV32_ADD(offset#MKPTR(v14$1), local_id_x$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(p10$2, BV32_ADD(offset#MKPTR(v14$2), local_id_x$2));
    assume {:do_not_predicate} {:check_id "check_state_4"} {:captureState "check_state_4"} {:sourceloc} {:sourceloc_num 29} true;
    call _CHECK_WRITE_$$A(p10$2, BV32_ADD(offset#MKPTR(v14$2), local_id_x$2), v9$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A"} true;
    $$A[BV32_ADD(offset#MKPTR(v14$1), local_id_x$1)] := (if p10$1 then v9$1 else $$A[BV32_ADD(offset#MKPTR(v14$1), local_id_x$1)]);
    $$A[BV32_ADD(offset#MKPTR(v14$2), local_id_x$2)] := (if p10$2 then v9$2 else $$A[BV32_ADD(offset#MKPTR(v14$2), local_id_x$2)]);
    p12$1 := (if p11$1 && base#MKPTR(v14$1) == $arrayId$$choice1 then base#MKPTR(v14$1) == $arrayId$$choice1 else p12$1);
    p12$2 := (if p11$2 && base#MKPTR(v14$2) == $arrayId$$choice1 then base#MKPTR(v14$2) == $arrayId$$choice1 else p12$2);
    p13$1 := (if p11$1 && base#MKPTR(v14$1) != $arrayId$$choice1 then base#MKPTR(v14$1) != $arrayId$$choice1 else p13$1);
    p13$2 := (if p11$2 && base#MKPTR(v14$2) != $arrayId$$choice1 then base#MKPTR(v14$2) != $arrayId$$choice1 else p13$2);
    $$choice1$1[BV32_ADD(offset#MKPTR(v14$1), local_id_x$1)] := (if p12$1 then v9$1 else $$choice1$1[BV32_ADD(offset#MKPTR(v14$1), local_id_x$1)]);
    $$choice1$2[BV32_ADD(offset#MKPTR(v14$2), local_id_x$2)] := (if p12$2 then v9$2 else $$choice1$2[BV32_ADD(offset#MKPTR(v14$2), local_id_x$2)]);
    p14$1 := (if p13$1 && base#MKPTR(v14$1) == $arrayId$$choice2 then base#MKPTR(v14$1) == $arrayId$$choice2 else p14$1);
    p14$2 := (if p13$2 && base#MKPTR(v14$2) == $arrayId$$choice2 then base#MKPTR(v14$2) == $arrayId$$choice2 else p14$2);
    p15$1 := (if p13$1 && base#MKPTR(v14$1) != $arrayId$$choice2 then base#MKPTR(v14$1) != $arrayId$$choice2 else p15$1);
    p15$2 := (if p13$2 && base#MKPTR(v14$2) != $arrayId$$choice2 then base#MKPTR(v14$2) != $arrayId$$choice2 else p15$2);
    $$choice2$1[BV32_ADD(offset#MKPTR(v14$1), local_id_x$1)] := (if p14$1 then v9$1 else $$choice2$1[BV32_ADD(offset#MKPTR(v14$1), local_id_x$1)]);
    $$choice2$2[BV32_ADD(offset#MKPTR(v14$2), local_id_x$2)] := (if p14$2 then v9$2 else $$choice2$2[BV32_ADD(offset#MKPTR(v14$2), local_id_x$2)]);
    assert {:bad_pointer_access} {:sourceloc_num 32} {:thread 1} p15$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 32} {:thread 2} p15$2 ==> false;
    v15$1 := $$choice1$1[0bv32];
    v15$2 := $$choice1$2[0bv32];
    v16$1 := $$choice1$1[1bv32];
    v16$2 := $$choice1$2[1bv32];
    v17$1 := $$choice1$1[2bv32];
    v17$2 := $$choice1$2[2bv32];
    v18$1 := $$choice1$1[3bv32];
    v18$2 := $$choice1$2[3bv32];
    $$choice2$1[0bv32] := v15$1;
    $$choice2$2[0bv32] := v15$2;
    $$choice2$1[1bv32] := v16$1;
    $$choice2$2[1bv32] := v16$2;
    $$choice2$1[2bv32] := v17$1;
    $$choice2$2[2bv32] := v17$2;
    $$choice2$1[3bv32] := v18$1;
    $$choice2$2[3bv32] := v18$2;
    v19$1 := $$choice1$1[0bv32];
    v19$2 := $$choice1$2[0bv32];
    v20$1 := $$choice1$1[1bv32];
    v20$2 := $$choice1$2[1bv32];
    v21$1 := $$choice1$1[2bv32];
    v21$2 := $$choice1$2[2bv32];
    v22$1 := $$choice1$1[3bv32];
    v22$2 := $$choice1$2[3bv32];
    v23$1 := v22$1 ++ v21$1 ++ v20$1 ++ v19$1;
    v23$2 := v22$2 ++ v21$2 ++ v20$2 ++ v19$2;
    p16$1 := (if base#MKPTR(v23$1) == $arrayId$$B then base#MKPTR(v23$1) == $arrayId$$B else p16$1);
    p16$2 := (if base#MKPTR(v23$2) == $arrayId$$B then base#MKPTR(v23$2) == $arrayId$$B else p16$2);
    p17$1 := (if base#MKPTR(v23$1) != $arrayId$$B then base#MKPTR(v23$1) != $arrayId$$B else p17$1);
    p17$2 := (if base#MKPTR(v23$2) != $arrayId$$B then base#MKPTR(v23$2) != $arrayId$$B else p17$2);
    call _LOG_READ_$$B(p16$1, BV32_ADD(offset#MKPTR(v23$1), local_id_x$1), $$B[BV32_ADD(offset#MKPTR(v23$1), local_id_x$1)]);
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 45} true;
    call _CHECK_READ_$$B(p16$2, BV32_ADD(offset#MKPTR(v23$2), local_id_x$2), $$B[BV32_ADD(offset#MKPTR(v23$2), local_id_x$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$B"} true;
    v24$1 := (if p16$1 then $$B[BV32_ADD(offset#MKPTR(v23$1), local_id_x$1)] else v24$1);
    v24$2 := (if p16$2 then $$B[BV32_ADD(offset#MKPTR(v23$2), local_id_x$2)] else v24$2);
    p18$1 := (if p17$1 && base#MKPTR(v23$1) == $arrayId$$A then base#MKPTR(v23$1) == $arrayId$$A else p18$1);
    p18$2 := (if p17$2 && base#MKPTR(v23$2) == $arrayId$$A then base#MKPTR(v23$2) == $arrayId$$A else p18$2);
    p19$1 := (if p17$1 && base#MKPTR(v23$1) != $arrayId$$A then base#MKPTR(v23$1) != $arrayId$$A else p19$1);
    p19$2 := (if p17$2 && base#MKPTR(v23$2) != $arrayId$$A then base#MKPTR(v23$2) != $arrayId$$A else p19$2);
    call _LOG_READ_$$A(p18$1, BV32_ADD(offset#MKPTR(v23$1), local_id_x$1), $$A[BV32_ADD(offset#MKPTR(v23$1), local_id_x$1)]);
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 46} true;
    call _CHECK_READ_$$A(p18$2, BV32_ADD(offset#MKPTR(v23$2), local_id_x$2), $$A[BV32_ADD(offset#MKPTR(v23$2), local_id_x$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    v24$1 := (if p18$1 then $$A[BV32_ADD(offset#MKPTR(v23$1), local_id_x$1)] else v24$1);
    v24$2 := (if p18$2 then $$A[BV32_ADD(offset#MKPTR(v23$2), local_id_x$2)] else v24$2);
    p20$1 := (if p19$1 && base#MKPTR(v23$1) == $arrayId$$choice1 then base#MKPTR(v23$1) == $arrayId$$choice1 else p20$1);
    p20$2 := (if p19$2 && base#MKPTR(v23$2) == $arrayId$$choice1 then base#MKPTR(v23$2) == $arrayId$$choice1 else p20$2);
    p21$1 := (if p19$1 && base#MKPTR(v23$1) != $arrayId$$choice1 then base#MKPTR(v23$1) != $arrayId$$choice1 else p21$1);
    p21$2 := (if p19$2 && base#MKPTR(v23$2) != $arrayId$$choice1 then base#MKPTR(v23$2) != $arrayId$$choice1 else p21$2);
    v24$1 := (if p20$1 then $$choice1$1[BV32_ADD(offset#MKPTR(v23$1), local_id_x$1)] else v24$1);
    v24$2 := (if p20$2 then $$choice1$2[BV32_ADD(offset#MKPTR(v23$2), local_id_x$2)] else v24$2);
    p22$1 := (if p21$1 && base#MKPTR(v23$1) == $arrayId$$choice2 then base#MKPTR(v23$1) == $arrayId$$choice2 else p22$1);
    p22$2 := (if p21$2 && base#MKPTR(v23$2) == $arrayId$$choice2 then base#MKPTR(v23$2) == $arrayId$$choice2 else p22$2);
    p23$1 := (if p21$1 && base#MKPTR(v23$1) != $arrayId$$choice2 then base#MKPTR(v23$1) != $arrayId$$choice2 else p23$1);
    p23$2 := (if p21$2 && base#MKPTR(v23$2) != $arrayId$$choice2 then base#MKPTR(v23$2) != $arrayId$$choice2 else p23$2);
    v24$1 := (if p22$1 then $$choice2$1[BV32_ADD(offset#MKPTR(v23$1), local_id_x$1)] else v24$1);
    v24$2 := (if p22$2 then $$choice2$2[BV32_ADD(offset#MKPTR(v23$2), local_id_x$2)] else v24$2);
    assert {:bad_pointer_access} {:sourceloc_num 49} {:thread 1} p23$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 49} {:thread 2} p23$2 ==> false;
    v25$1 := $$choice2$1[0bv32];
    v25$2 := $$choice2$2[0bv32];
    v26$1 := $$choice2$1[1bv32];
    v26$2 := $$choice2$2[1bv32];
    v27$1 := $$choice2$1[2bv32];
    v27$2 := $$choice2$2[2bv32];
    v28$1 := $$choice2$1[3bv32];
    v28$2 := $$choice2$2[3bv32];
    v29$1 := v28$1 ++ v27$1 ++ v26$1 ++ v25$1;
    v29$2 := v28$2 ++ v27$2 ++ v26$2 ++ v25$2;
    p24$1 := (if base#MKPTR(v29$1) == $arrayId$$B then base#MKPTR(v29$1) == $arrayId$$B else p24$1);
    p24$2 := (if base#MKPTR(v29$2) == $arrayId$$B then base#MKPTR(v29$2) == $arrayId$$B else p24$2);
    p25$1 := (if base#MKPTR(v29$1) != $arrayId$$B then base#MKPTR(v29$1) != $arrayId$$B else p25$1);
    p25$2 := (if base#MKPTR(v29$2) != $arrayId$$B then base#MKPTR(v29$2) != $arrayId$$B else p25$2);
    call _LOG_WRITE_$$B(p24$1, BV32_ADD(offset#MKPTR(v29$1), local_id_x$1), v24$1, $$B[BV32_ADD(offset#MKPTR(v29$1), local_id_x$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$B(p24$2, BV32_ADD(offset#MKPTR(v29$2), local_id_x$2));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 54} true;
    call _CHECK_WRITE_$$B(p24$2, BV32_ADD(offset#MKPTR(v29$2), local_id_x$2), v24$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$B"} true;
    $$B[BV32_ADD(offset#MKPTR(v29$1), local_id_x$1)] := (if p24$1 then v24$1 else $$B[BV32_ADD(offset#MKPTR(v29$1), local_id_x$1)]);
    $$B[BV32_ADD(offset#MKPTR(v29$2), local_id_x$2)] := (if p24$2 then v24$2 else $$B[BV32_ADD(offset#MKPTR(v29$2), local_id_x$2)]);
    p26$1 := (if p25$1 && base#MKPTR(v29$1) == $arrayId$$A then base#MKPTR(v29$1) == $arrayId$$A else p26$1);
    p26$2 := (if p25$2 && base#MKPTR(v29$2) == $arrayId$$A then base#MKPTR(v29$2) == $arrayId$$A else p26$2);
    p27$1 := (if p25$1 && base#MKPTR(v29$1) != $arrayId$$A then base#MKPTR(v29$1) != $arrayId$$A else p27$1);
    p27$2 := (if p25$2 && base#MKPTR(v29$2) != $arrayId$$A then base#MKPTR(v29$2) != $arrayId$$A else p27$2);
    call _LOG_WRITE_$$A(p26$1, BV32_ADD(offset#MKPTR(v29$1), local_id_x$1), v24$1, $$A[BV32_ADD(offset#MKPTR(v29$1), local_id_x$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(p26$2, BV32_ADD(offset#MKPTR(v29$2), local_id_x$2));
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 55} true;
    call _CHECK_WRITE_$$A(p26$2, BV32_ADD(offset#MKPTR(v29$2), local_id_x$2), v24$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A"} true;
    $$A[BV32_ADD(offset#MKPTR(v29$1), local_id_x$1)] := (if p26$1 then v24$1 else $$A[BV32_ADD(offset#MKPTR(v29$1), local_id_x$1)]);
    $$A[BV32_ADD(offset#MKPTR(v29$2), local_id_x$2)] := (if p26$2 then v24$2 else $$A[BV32_ADD(offset#MKPTR(v29$2), local_id_x$2)]);
    p28$1 := (if p27$1 && base#MKPTR(v29$1) == $arrayId$$choice1 then base#MKPTR(v29$1) == $arrayId$$choice1 else p28$1);
    p28$2 := (if p27$2 && base#MKPTR(v29$2) == $arrayId$$choice1 then base#MKPTR(v29$2) == $arrayId$$choice1 else p28$2);
    p29$1 := (if p27$1 && base#MKPTR(v29$1) != $arrayId$$choice1 then base#MKPTR(v29$1) != $arrayId$$choice1 else p29$1);
    p29$2 := (if p27$2 && base#MKPTR(v29$2) != $arrayId$$choice1 then base#MKPTR(v29$2) != $arrayId$$choice1 else p29$2);
    $$choice1$1[BV32_ADD(offset#MKPTR(v29$1), local_id_x$1)] := (if p28$1 then v24$1 else $$choice1$1[BV32_ADD(offset#MKPTR(v29$1), local_id_x$1)]);
    $$choice1$2[BV32_ADD(offset#MKPTR(v29$2), local_id_x$2)] := (if p28$2 then v24$2 else $$choice1$2[BV32_ADD(offset#MKPTR(v29$2), local_id_x$2)]);
    p30$1 := (if p29$1 && base#MKPTR(v29$1) == $arrayId$$choice2 then base#MKPTR(v29$1) == $arrayId$$choice2 else p30$1);
    p30$2 := (if p29$2 && base#MKPTR(v29$2) == $arrayId$$choice2 then base#MKPTR(v29$2) == $arrayId$$choice2 else p30$2);
    p31$1 := (if p29$1 && base#MKPTR(v29$1) != $arrayId$$choice2 then base#MKPTR(v29$1) != $arrayId$$choice2 else p31$1);
    p31$2 := (if p29$2 && base#MKPTR(v29$2) != $arrayId$$choice2 then base#MKPTR(v29$2) != $arrayId$$choice2 else p31$2);
    $$choice2$1[BV32_ADD(offset#MKPTR(v29$1), local_id_x$1)] := (if p30$1 then v24$1 else $$choice2$1[BV32_ADD(offset#MKPTR(v29$1), local_id_x$1)]);
    $$choice2$2[BV32_ADD(offset#MKPTR(v29$2), local_id_x$2)] := (if p30$2 then v24$2 else $$choice2$2[BV32_ADD(offset#MKPTR(v29$2), local_id_x$2)]);
    assert {:bad_pointer_access} {:sourceloc_num 58} {:thread 1} p31$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 58} {:thread 2} p31$2 ==> false;
    v30$1 := $$choice1$1[0bv32];
    v30$2 := $$choice1$2[0bv32];
    v31$1 := $$choice1$1[1bv32];
    v31$2 := $$choice1$2[1bv32];
    v32$1 := $$choice1$1[2bv32];
    v32$2 := $$choice1$2[2bv32];
    v33$1 := $$choice1$1[3bv32];
    v33$2 := $$choice1$2[3bv32];
    $$choice2$1[0bv32] := v30$1;
    $$choice2$2[0bv32] := v30$2;
    $$choice2$1[1bv32] := v31$1;
    $$choice2$2[1bv32] := v31$2;
    $$choice2$1[2bv32] := v32$1;
    $$choice2$2[2bv32] := v32$2;
    $$choice2$1[3bv32] := v33$1;
    $$choice2$2[3bv32] := v33$2;
    return;

  $truebb0:
    assume {:partition} v2;
    $cond5 := MKPTR($arrayId$$B, 0bv32);
    goto $cond.end4;

  $truebb:
    assume {:partition} v0;
    $cond := MKPTR($arrayId$$A, 0bv32);
    goto $cond.end;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 1024bv32 then 1bv1 else 0bv1) != 0bv1;

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

const _WATCHED_VALUE_$$A: bv8;

procedure {:inline 1} _LOG_READ_$$A(_P: bool, _offset: bv32, _value: bv8);
  modifies _READ_HAS_OCCURRED_$$A;

implementation {:inline 1} _LOG_READ_$$A(_P: bool, _offset: bv32, _value: bv8)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$A := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A == _value then true else _READ_HAS_OCCURRED_$$A);
    return;
}

procedure _CHECK_READ_$$A(_P: bool, _offset: bv32, _value: bv8);
  requires !(_P && _WRITE_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$A);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$A: bool;

procedure {:inline 1} _LOG_WRITE_$$A(_P: bool, _offset: bv32, _value: bv8, _value_old: bv8);
  modifies _WRITE_HAS_OCCURRED_$$A, _WRITE_READ_BENIGN_FLAG_$$A;

implementation {:inline 1} _LOG_WRITE_$$A(_P: bool, _offset: bv32, _value: bv8, _value_old: bv8)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$A := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A == _value then true else _WRITE_HAS_OCCURRED_$$A);
    _WRITE_READ_BENIGN_FLAG_$$A := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$A);
    return;
}

procedure _CHECK_WRITE_$$A(_P: bool, _offset: bv32, _value: bv8);
  requires !(_P && _WRITE_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$A(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$A;

implementation {:inline 1} _LOG_ATOMIC_$$A(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$A := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$A);
    return;
}

procedure _CHECK_ATOMIC_$$A(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$A;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$A := (if _P && _WRITE_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$A);
    return;
}

const _WATCHED_VALUE_$$B: bv8;

procedure {:inline 1} _LOG_READ_$$B(_P: bool, _offset: bv32, _value: bv8);
  modifies _READ_HAS_OCCURRED_$$B;

implementation {:inline 1} _LOG_READ_$$B(_P: bool, _offset: bv32, _value: bv8)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$B := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$B == _value then true else _READ_HAS_OCCURRED_$$B);
    return;
}

procedure _CHECK_READ_$$B(_P: bool, _offset: bv32, _value: bv8);
  requires !(_P && _WRITE_HAS_OCCURRED_$$B && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$B);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$B && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$B: bool;

procedure {:inline 1} _LOG_WRITE_$$B(_P: bool, _offset: bv32, _value: bv8, _value_old: bv8);
  modifies _WRITE_HAS_OCCURRED_$$B, _WRITE_READ_BENIGN_FLAG_$$B;

implementation {:inline 1} _LOG_WRITE_$$B(_P: bool, _offset: bv32, _value: bv8, _value_old: bv8)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$B := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$B == _value then true else _WRITE_HAS_OCCURRED_$$B);
    _WRITE_READ_BENIGN_FLAG_$$B := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$B == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$B);
    return;
}

procedure _CHECK_WRITE_$$B(_P: bool, _offset: bv32, _value: bv8);
  requires !(_P && _WRITE_HAS_OCCURRED_$$B && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$B != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$B && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$B != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$B && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$B(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$B;

implementation {:inline 1} _LOG_ATOMIC_$$B(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$B := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$B);
    return;
}

procedure _CHECK_ATOMIC_$$B(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$B && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$B && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$B(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$B;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$B(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$B := (if _P && _WRITE_HAS_OCCURRED_$$B && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$B);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
