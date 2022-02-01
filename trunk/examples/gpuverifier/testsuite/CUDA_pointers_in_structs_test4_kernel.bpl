//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP8(x: [bv32]bv8, y: bv32) returns (z$1: bv8, A$1: [bv32]bv8, z$2: bv8, A$2: [bv32]bv8);

var {:source_name "A.coerce0.coerce0"} {:global} $$A.coerce0.coerce0: [bv32]bv8;

axiom {:array_info "$$A.coerce0.coerce0"} {:global} {:elem_width 8} {:source_name "A.coerce0.coerce0"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$A.coerce0.coerce0: bool;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$A.coerce0.coerce0: bool;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$A.coerce0.coerce0: bool;

const $arrayId$$A.coerce0.coerce0: arrayId;

axiom $arrayId$$A.coerce0.coerce0 == 1bv3;

var {:source_name "A.coerce0.coerce1"} {:global} $$A.coerce0.coerce1: [bv32]bv8;

axiom {:array_info "$$A.coerce0.coerce1"} {:global} {:elem_width 8} {:source_name "A.coerce0.coerce1"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$A.coerce0.coerce1: bool;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$A.coerce0.coerce1: bool;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$A.coerce0.coerce1: bool;

const $arrayId$$A.coerce0.coerce1: arrayId;

axiom $arrayId$$A.coerce0.coerce1 == 2bv3;

var {:source_name "A.val"} $$A.val$1: [bv32]bv8;

var {:source_name "A.val"} $$A.val$2: [bv32]bv8;

axiom {:array_info "$$A.val"} {:elem_width 8} {:source_name "A.val"} {:source_elem_width 64} {:source_dimensions "1"} true;

const $arrayId$$A.val: arrayId;

axiom $arrayId$$A.val == 3bv3;

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

procedure {:source_name "foo"} ULTIMATE.start($A: bv64);
  requires $A[32:0] == MKPTR($arrayId$$A.coerce0.coerce0, 0bv32);
  requires $A[64:32] == MKPTR($arrayId$$A.coerce0.coerce1, 0bv32);
  requires !_READ_HAS_OCCURRED_$$A.coerce0.coerce0 && !_WRITE_HAS_OCCURRED_$$A.coerce0.coerce0 && !_ATOMIC_HAS_OCCURRED_$$A.coerce0.coerce0;
  requires !_READ_HAS_OCCURRED_$$A.coerce0.coerce1 && !_WRITE_HAS_OCCURRED_$$A.coerce0.coerce1 && !_ATOMIC_HAS_OCCURRED_$$A.coerce0.coerce1;
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
  modifies _READ_HAS_OCCURRED_$$A.coerce0.coerce0, _READ_HAS_OCCURRED_$$A.coerce0.coerce1, _WRITE_HAS_OCCURRED_$$A.coerce0.coerce0, _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0, _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0, _WRITE_HAS_OCCURRED_$$A.coerce0.coerce1, _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1, _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1;

implementation {:source_name "foo"} ULTIMATE.start($A: bv64)
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
  var v5$1: bv8;
  var v5$2: bv8;
  var v6$1: bv8;
  var v6$2: bv8;
  var v7$1: bv8;
  var v7$2: bv8;
  var v8$1: bv8;
  var v8$2: bv8;
  var v9$1: bv32;
  var v9$2: bv32;
  var v10$1: bv8;
  var v10$2: bv8;
  var v11$1: bv8;
  var v11$2: bv8;
  var v12$1: bv8;
  var v12$2: bv8;
  var v13$1: bv8;
  var v13$2: bv8;
  var v14$1: ptr;
  var v14$2: ptr;
  var v16$1: bv8;
  var v16$2: bv8;
  var v15$1: bv8;
  var v15$2: bv8;
  var v17$1: bv8;
  var v17$2: bv8;
  var v18$1: bv8;
  var v18$2: bv8;
  var v19$1: ptr;
  var v19$2: ptr;
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
  var p32$1: bool;
  var p32$2: bool;
  var p33$1: bool;
  var p33$2: bool;
  var p34$1: bool;
  var p34$2: bool;
  var p35$1: bool;
  var p35$2: bool;
  var p36$1: bool;
  var p36$2: bool;
  var p37$1: bool;
  var p37$2: bool;
  var p38$1: bool;
  var p38$2: bool;
  var p39$1: bool;
  var p39$2: bool;
  var p40$1: bool;
  var p40$2: bool;
  var p41$1: bool;
  var p41$2: bool;
  var p42$1: bool;
  var p42$2: bool;
  var p43$1: bool;
  var p43$2: bool;
  var p44$1: bool;
  var p44$2: bool;
  var p45$1: bool;
  var p45$2: bool;
  var p46$1: bool;
  var p46$2: bool;
  var p47$1: bool;
  var p47$2: bool;
  var p48$1: bool;
  var p48$2: bool;
  var p49$1: bool;
  var p49$2: bool;
  var p50$1: bool;
  var p50$2: bool;
  var p51$1: bool;
  var p51$2: bool;
  var p52$1: bool;
  var p52$2: bool;
  var p53$1: bool;
  var p53$2: bool;
  var p54$1: bool;
  var p54$2: bool;
  var p55$1: bool;
  var p55$2: bool;
  var p56$1: bool;
  var p56$2: bool;
  var p57$1: bool;
  var p57$2: bool;
  var p58$1: bool;
  var p58$2: bool;
  var p59$1: bool;
  var p59$2: bool;
  var p60$1: bool;
  var p60$2: bool;
  var p61$1: bool;
  var p61$2: bool;
  var p62$1: bool;
  var p62$2: bool;
  var p63$1: bool;
  var p63$2: bool;
  var p64$1: bool;
  var p64$2: bool;
  var p65$1: bool;
  var p65$2: bool;
  var p66$1: bool;
  var p66$2: bool;
  var p67$1: bool;
  var p67$2: bool;
  var p68$1: bool;
  var p68$2: bool;
  var p69$1: bool;
  var p69$2: bool;
  var p70$1: bool;
  var p70$2: bool;
  var p71$1: bool;
  var p71$2: bool;

  $entry:
    $$A.val$1[0bv32] := $A[8:0];
    $$A.val$2[0bv32] := $A[8:0];
    $$A.val$1[1bv32] := $A[16:8];
    $$A.val$2[1bv32] := $A[16:8];
    $$A.val$1[2bv32] := $A[24:16];
    $$A.val$2[2bv32] := $A[24:16];
    $$A.val$1[3bv32] := $A[32:24];
    $$A.val$2[3bv32] := $A[32:24];
    $$A.val$1[4bv32] := $A[40:32];
    $$A.val$2[4bv32] := $A[40:32];
    $$A.val$1[5bv32] := $A[48:40];
    $$A.val$2[5bv32] := $A[48:40];
    $$A.val$1[6bv32] := $A[56:48];
    $$A.val$2[6bv32] := $A[56:48];
    $$A.val$1[7bv32] := $A[64:56];
    $$A.val$2[7bv32] := $A[64:56];
    v0$1 := $$A.val$1[4bv32];
    v0$2 := $$A.val$2[4bv32];
    v1$1 := $$A.val$1[5bv32];
    v1$2 := $$A.val$2[5bv32];
    v2$1 := $$A.val$1[6bv32];
    v2$2 := $$A.val$2[6bv32];
    v3$1 := $$A.val$1[7bv32];
    v3$2 := $$A.val$2[7bv32];
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
    p32$1 := false;
    p32$2 := false;
    p33$1 := false;
    p33$2 := false;
    p34$1 := false;
    p34$2 := false;
    p35$1 := false;
    p35$2 := false;
    p36$1 := false;
    p36$2 := false;
    p37$1 := false;
    p37$2 := false;
    p38$1 := false;
    p38$2 := false;
    p39$1 := false;
    p39$2 := false;
    p40$1 := false;
    p40$2 := false;
    p41$1 := false;
    p41$2 := false;
    p42$1 := false;
    p42$2 := false;
    p43$1 := false;
    p43$2 := false;
    p44$1 := false;
    p44$2 := false;
    p45$1 := false;
    p45$2 := false;
    p46$1 := false;
    p46$2 := false;
    p47$1 := false;
    p47$2 := false;
    p48$1 := false;
    p48$2 := false;
    p49$1 := false;
    p49$2 := false;
    p50$1 := false;
    p50$2 := false;
    p51$1 := false;
    p51$2 := false;
    p52$1 := false;
    p52$2 := false;
    p53$1 := false;
    p53$2 := false;
    p54$1 := false;
    p54$2 := false;
    p55$1 := false;
    p55$2 := false;
    p56$1 := false;
    p56$2 := false;
    p57$1 := false;
    p57$2 := false;
    p58$1 := false;
    p58$2 := false;
    p59$1 := false;
    p59$2 := false;
    p60$1 := false;
    p60$2 := false;
    p61$1 := false;
    p61$2 := false;
    p62$1 := false;
    p62$2 := false;
    p63$1 := false;
    p63$2 := false;
    p64$1 := false;
    p64$2 := false;
    p65$1 := false;
    p65$2 := false;
    p66$1 := false;
    p66$2 := false;
    p67$1 := false;
    p67$2 := false;
    p68$1 := false;
    p68$2 := false;
    p69$1 := false;
    p69$2 := false;
    p70$1 := false;
    p70$2 := false;
    p71$1 := false;
    p71$2 := false;
    p0$1 := (if base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce0 else p0$1);
    p0$2 := (if base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce0 else p0$2);
    p1$1 := (if base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce0 else p1$1);
    p1$2 := (if base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce0 else p1$2);
    call _LOG_READ_$$A.coerce0.coerce0(p0$1, BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))]);
    assume {:do_not_predicate} {:check_id "check_state_23"} {:captureState "check_state_23"} {:sourceloc} {:sourceloc_num 5} true;
    call _CHECK_READ_$$A.coerce0.coerce0(p0$2, BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A.coerce0.coerce0"} true;
    v5$1 := (if p0$1 then $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))] else v5$1);
    v5$2 := (if p0$2 then $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))] else v5$2);
    p2$1 := (if p1$1 && base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce1 else p2$1);
    p2$2 := (if p1$2 && base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce1 else p2$2);
    p3$1 := (if p1$1 && base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce1 else p3$1);
    p3$2 := (if p1$2 && base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce1 else p3$2);
    call _LOG_READ_$$A.coerce0.coerce1(p2$1, BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), $$A.coerce0.coerce1[BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))]);
    assume {:do_not_predicate} {:check_id "check_state_22"} {:captureState "check_state_22"} {:sourceloc} {:sourceloc_num 6} true;
    call _CHECK_READ_$$A.coerce0.coerce1(p2$2, BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), $$A.coerce0.coerce1[BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A.coerce0.coerce1"} true;
    v5$1 := (if p2$1 then $$A.coerce0.coerce1[BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))] else v5$1);
    v5$2 := (if p2$2 then $$A.coerce0.coerce1[BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))] else v5$2);
    p4$1 := (if p3$1 && base#MKPTR(v4$1) == $arrayId$$A.val then base#MKPTR(v4$1) == $arrayId$$A.val else p4$1);
    p4$2 := (if p3$2 && base#MKPTR(v4$2) == $arrayId$$A.val then base#MKPTR(v4$2) == $arrayId$$A.val else p4$2);
    p5$1 := (if p3$1 && base#MKPTR(v4$1) != $arrayId$$A.val then base#MKPTR(v4$1) != $arrayId$$A.val else p5$1);
    p5$2 := (if p3$2 && base#MKPTR(v4$2) != $arrayId$$A.val then base#MKPTR(v4$2) != $arrayId$$A.val else p5$2);
    v5$1 := (if p4$1 then $$A.val$1[BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))] else v5$1);
    v5$2 := (if p4$2 then $$A.val$2[BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))] else v5$2);
    assert {:bad_pointer_access} {:sourceloc_num 8} {:thread 1} p5$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 8} {:thread 2} p5$2 ==> false;
    p6$1 := (if base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce0 else p6$1);
    p6$2 := (if base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce0 else p6$2);
    p7$1 := (if base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce0 else p7$1);
    p7$2 := (if base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce0 else p7$2);
    call _LOG_READ_$$A.coerce0.coerce0(p6$1, BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32), $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_21"} {:captureState "check_state_21"} {:sourceloc} {:sourceloc_num 9} true;
    call _CHECK_READ_$$A.coerce0.coerce0(p6$2, BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32), $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A.coerce0.coerce0"} true;
    v6$1 := (if p6$1 then $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)] else v6$1);
    v6$2 := (if p6$2 then $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)] else v6$2);
    p8$1 := (if p7$1 && base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce1 else p8$1);
    p8$2 := (if p7$2 && base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce1 else p8$2);
    p9$1 := (if p7$1 && base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce1 else p9$1);
    p9$2 := (if p7$2 && base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce1 else p9$2);
    call _LOG_READ_$$A.coerce0.coerce1(p8$1, BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32), $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_20"} {:captureState "check_state_20"} {:sourceloc} {:sourceloc_num 10} true;
    call _CHECK_READ_$$A.coerce0.coerce1(p8$2, BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32), $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A.coerce0.coerce1"} true;
    v6$1 := (if p8$1 then $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)] else v6$1);
    v6$2 := (if p8$2 then $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)] else v6$2);
    p10$1 := (if p9$1 && base#MKPTR(v4$1) == $arrayId$$A.val then base#MKPTR(v4$1) == $arrayId$$A.val else p10$1);
    p10$2 := (if p9$2 && base#MKPTR(v4$2) == $arrayId$$A.val then base#MKPTR(v4$2) == $arrayId$$A.val else p10$2);
    p11$1 := (if p9$1 && base#MKPTR(v4$1) != $arrayId$$A.val then base#MKPTR(v4$1) != $arrayId$$A.val else p11$1);
    p11$2 := (if p9$2 && base#MKPTR(v4$2) != $arrayId$$A.val then base#MKPTR(v4$2) != $arrayId$$A.val else p11$2);
    v6$1 := (if p10$1 then $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)] else v6$1);
    v6$2 := (if p10$2 then $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)] else v6$2);
    assert {:bad_pointer_access} {:sourceloc_num 12} {:thread 1} p11$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 12} {:thread 2} p11$2 ==> false;
    p12$1 := (if base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce0 else p12$1);
    p12$2 := (if base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce0 else p12$2);
    p13$1 := (if base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce0 else p13$1);
    p13$2 := (if base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce0 else p13$2);
    call _LOG_READ_$$A.coerce0.coerce0(p12$1, BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32), $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_19"} {:captureState "check_state_19"} {:sourceloc} {:sourceloc_num 13} true;
    call _CHECK_READ_$$A.coerce0.coerce0(p12$2, BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32), $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A.coerce0.coerce0"} true;
    v7$1 := (if p12$1 then $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)] else v7$1);
    v7$2 := (if p12$2 then $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)] else v7$2);
    p14$1 := (if p13$1 && base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce1 else p14$1);
    p14$2 := (if p13$2 && base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce1 else p14$2);
    p15$1 := (if p13$1 && base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce1 else p15$1);
    p15$2 := (if p13$2 && base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce1 else p15$2);
    call _LOG_READ_$$A.coerce0.coerce1(p14$1, BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32), $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_18"} {:captureState "check_state_18"} {:sourceloc} {:sourceloc_num 14} true;
    call _CHECK_READ_$$A.coerce0.coerce1(p14$2, BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32), $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A.coerce0.coerce1"} true;
    v7$1 := (if p14$1 then $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)] else v7$1);
    v7$2 := (if p14$2 then $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)] else v7$2);
    p16$1 := (if p15$1 && base#MKPTR(v4$1) == $arrayId$$A.val then base#MKPTR(v4$1) == $arrayId$$A.val else p16$1);
    p16$2 := (if p15$2 && base#MKPTR(v4$2) == $arrayId$$A.val then base#MKPTR(v4$2) == $arrayId$$A.val else p16$2);
    p17$1 := (if p15$1 && base#MKPTR(v4$1) != $arrayId$$A.val then base#MKPTR(v4$1) != $arrayId$$A.val else p17$1);
    p17$2 := (if p15$2 && base#MKPTR(v4$2) != $arrayId$$A.val then base#MKPTR(v4$2) != $arrayId$$A.val else p17$2);
    v7$1 := (if p16$1 then $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)] else v7$1);
    v7$2 := (if p16$2 then $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)] else v7$2);
    assert {:bad_pointer_access} {:sourceloc_num 16} {:thread 1} p17$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 16} {:thread 2} p17$2 ==> false;
    p18$1 := (if base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce0 else p18$1);
    p18$2 := (if base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce0 else p18$2);
    p19$1 := (if base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce0 else p19$1);
    p19$2 := (if base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce0 else p19$2);
    call _LOG_READ_$$A.coerce0.coerce0(p18$1, BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32), $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_17"} {:captureState "check_state_17"} {:sourceloc} {:sourceloc_num 17} true;
    call _CHECK_READ_$$A.coerce0.coerce0(p18$2, BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32), $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A.coerce0.coerce0"} true;
    v8$1 := (if p18$1 then $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)] else v8$1);
    v8$2 := (if p18$2 then $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)] else v8$2);
    p20$1 := (if p19$1 && base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v4$1) == $arrayId$$A.coerce0.coerce1 else p20$1);
    p20$2 := (if p19$2 && base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v4$2) == $arrayId$$A.coerce0.coerce1 else p20$2);
    p21$1 := (if p19$1 && base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v4$1) != $arrayId$$A.coerce0.coerce1 else p21$1);
    p21$2 := (if p19$2 && base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v4$2) != $arrayId$$A.coerce0.coerce1 else p21$2);
    call _LOG_READ_$$A.coerce0.coerce1(p20$1, BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32), $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_16"} {:captureState "check_state_16"} {:sourceloc} {:sourceloc_num 18} true;
    call _CHECK_READ_$$A.coerce0.coerce1(p20$2, BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32), $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A.coerce0.coerce1"} true;
    v8$1 := (if p20$1 then $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)] else v8$1);
    v8$2 := (if p20$2 then $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)] else v8$2);
    p22$1 := (if p21$1 && base#MKPTR(v4$1) == $arrayId$$A.val then base#MKPTR(v4$1) == $arrayId$$A.val else p22$1);
    p22$2 := (if p21$2 && base#MKPTR(v4$2) == $arrayId$$A.val then base#MKPTR(v4$2) == $arrayId$$A.val else p22$2);
    p23$1 := (if p21$1 && base#MKPTR(v4$1) != $arrayId$$A.val then base#MKPTR(v4$1) != $arrayId$$A.val else p23$1);
    p23$2 := (if p21$2 && base#MKPTR(v4$2) != $arrayId$$A.val then base#MKPTR(v4$2) != $arrayId$$A.val else p23$2);
    v8$1 := (if p22$1 then $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v4$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)] else v8$1);
    v8$2 := (if p22$2 then $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v4$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)] else v8$2);
    assert {:bad_pointer_access} {:sourceloc_num 20} {:thread 1} p23$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 20} {:thread 2} p23$2 ==> false;
    v9$1 := BV32_ADD(v8$1 ++ v7$1 ++ v6$1 ++ v5$1, local_id_x$1);
    v9$2 := BV32_ADD(v8$2 ++ v7$2 ++ v6$2 ++ v5$2, local_id_x$2);
    v10$1 := $$A.val$1[0bv32];
    v10$2 := $$A.val$2[0bv32];
    v11$1 := $$A.val$1[1bv32];
    v11$2 := $$A.val$2[1bv32];
    v12$1 := $$A.val$1[2bv32];
    v12$2 := $$A.val$2[2bv32];
    v13$1 := $$A.val$1[3bv32];
    v13$2 := $$A.val$2[3bv32];
    v14$1 := v13$1 ++ v12$1 ++ v11$1 ++ v10$1;
    v14$2 := v13$2 ++ v12$2 ++ v11$2 ++ v10$2;
    p24$1 := (if base#MKPTR(v14$1) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v14$1) == $arrayId$$A.coerce0.coerce0 else p24$1);
    p24$2 := (if base#MKPTR(v14$2) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v14$2) == $arrayId$$A.coerce0.coerce0 else p24$2);
    p25$1 := (if base#MKPTR(v14$1) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v14$1) != $arrayId$$A.coerce0.coerce0 else p25$1);
    p25$2 := (if base#MKPTR(v14$2) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v14$2) != $arrayId$$A.coerce0.coerce0 else p25$2);
    call _LOG_WRITE_$$A.coerce0.coerce0(p24$1, BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), v9$1[8:0], $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0(p24$2, BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)));
    assume {:do_not_predicate} {:check_id "check_state_15"} {:captureState "check_state_15"} {:sourceloc} {:sourceloc_num 25} true;
    call _CHECK_WRITE_$$A.coerce0.coerce0(p24$2, BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), v9$2[8:0]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce0"} true;
    $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))] := (if p24$1 then v9$1[8:0] else $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))]);
    $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))] := (if p24$2 then v9$2[8:0] else $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))]);
    p26$1 := (if p25$1 && base#MKPTR(v14$1) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v14$1) == $arrayId$$A.coerce0.coerce1 else p26$1);
    p26$2 := (if p25$2 && base#MKPTR(v14$2) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v14$2) == $arrayId$$A.coerce0.coerce1 else p26$2);
    p27$1 := (if p25$1 && base#MKPTR(v14$1) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v14$1) != $arrayId$$A.coerce0.coerce1 else p27$1);
    p27$2 := (if p25$2 && base#MKPTR(v14$2) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v14$2) != $arrayId$$A.coerce0.coerce1 else p27$2);
    call _LOG_WRITE_$$A.coerce0.coerce1(p26$1, BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), v9$1[8:0], $$A.coerce0.coerce1[BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1(p26$2, BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)));
    assume {:do_not_predicate} {:check_id "check_state_14"} {:captureState "check_state_14"} {:sourceloc} {:sourceloc_num 26} true;
    call _CHECK_WRITE_$$A.coerce0.coerce1(p26$2, BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), v9$2[8:0]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce1"} true;
    $$A.coerce0.coerce1[BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))] := (if p26$1 then v9$1[8:0] else $$A.coerce0.coerce1[BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))]);
    $$A.coerce0.coerce1[BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))] := (if p26$2 then v9$2[8:0] else $$A.coerce0.coerce1[BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))]);
    p28$1 := (if p27$1 && base#MKPTR(v14$1) == $arrayId$$A.val then base#MKPTR(v14$1) == $arrayId$$A.val else p28$1);
    p28$2 := (if p27$2 && base#MKPTR(v14$2) == $arrayId$$A.val then base#MKPTR(v14$2) == $arrayId$$A.val else p28$2);
    p29$1 := (if p27$1 && base#MKPTR(v14$1) != $arrayId$$A.val then base#MKPTR(v14$1) != $arrayId$$A.val else p29$1);
    p29$2 := (if p27$2 && base#MKPTR(v14$2) != $arrayId$$A.val then base#MKPTR(v14$2) != $arrayId$$A.val else p29$2);
    $$A.val$1[BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))] := (if p28$1 then v9$1[8:0] else $$A.val$1[BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))]);
    $$A.val$2[BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))] := (if p28$2 then v9$2[8:0] else $$A.val$2[BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))]);
    assert {:bad_pointer_access} {:sourceloc_num 28} {:thread 1} p29$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 28} {:thread 2} p29$2 ==> false;
    p30$1 := (if base#MKPTR(v14$1) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v14$1) == $arrayId$$A.coerce0.coerce0 else p30$1);
    p30$2 := (if base#MKPTR(v14$2) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v14$2) == $arrayId$$A.coerce0.coerce0 else p30$2);
    p31$1 := (if base#MKPTR(v14$1) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v14$1) != $arrayId$$A.coerce0.coerce0 else p31$1);
    p31$2 := (if base#MKPTR(v14$2) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v14$2) != $arrayId$$A.coerce0.coerce0 else p31$2);
    call _LOG_WRITE_$$A.coerce0.coerce0(p30$1, BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32), v9$1[16:8], $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0(p30$2, BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_13"} {:captureState "check_state_13"} {:sourceloc} {:sourceloc_num 29} true;
    call _CHECK_WRITE_$$A.coerce0.coerce0(p30$2, BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32), v9$2[16:8]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce0"} true;
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)] := (if p30$1 then v9$1[16:8] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)]);
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)] := (if p30$2 then v9$2[16:8] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)]);
    p32$1 := (if p31$1 && base#MKPTR(v14$1) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v14$1) == $arrayId$$A.coerce0.coerce1 else p32$1);
    p32$2 := (if p31$2 && base#MKPTR(v14$2) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v14$2) == $arrayId$$A.coerce0.coerce1 else p32$2);
    p33$1 := (if p31$1 && base#MKPTR(v14$1) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v14$1) != $arrayId$$A.coerce0.coerce1 else p33$1);
    p33$2 := (if p31$2 && base#MKPTR(v14$2) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v14$2) != $arrayId$$A.coerce0.coerce1 else p33$2);
    call _LOG_WRITE_$$A.coerce0.coerce1(p32$1, BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32), v9$1[16:8], $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1(p32$2, BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_12"} {:captureState "check_state_12"} {:sourceloc} {:sourceloc_num 30} true;
    call _CHECK_WRITE_$$A.coerce0.coerce1(p32$2, BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32), v9$2[16:8]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce1"} true;
    $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)] := (if p32$1 then v9$1[16:8] else $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)]);
    $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)] := (if p32$2 then v9$2[16:8] else $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)]);
    p34$1 := (if p33$1 && base#MKPTR(v14$1) == $arrayId$$A.val then base#MKPTR(v14$1) == $arrayId$$A.val else p34$1);
    p34$2 := (if p33$2 && base#MKPTR(v14$2) == $arrayId$$A.val then base#MKPTR(v14$2) == $arrayId$$A.val else p34$2);
    p35$1 := (if p33$1 && base#MKPTR(v14$1) != $arrayId$$A.val then base#MKPTR(v14$1) != $arrayId$$A.val else p35$1);
    p35$2 := (if p33$2 && base#MKPTR(v14$2) != $arrayId$$A.val then base#MKPTR(v14$2) != $arrayId$$A.val else p35$2);
    $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)] := (if p34$1 then v9$1[16:8] else $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)]);
    $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)] := (if p34$2 then v9$2[16:8] else $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)]);
    assert {:bad_pointer_access} {:sourceloc_num 32} {:thread 1} p35$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 32} {:thread 2} p35$2 ==> false;
    p36$1 := (if base#MKPTR(v14$1) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v14$1) == $arrayId$$A.coerce0.coerce0 else p36$1);
    p36$2 := (if base#MKPTR(v14$2) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v14$2) == $arrayId$$A.coerce0.coerce0 else p36$2);
    p37$1 := (if base#MKPTR(v14$1) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v14$1) != $arrayId$$A.coerce0.coerce0 else p37$1);
    p37$2 := (if base#MKPTR(v14$2) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v14$2) != $arrayId$$A.coerce0.coerce0 else p37$2);
    call _LOG_WRITE_$$A.coerce0.coerce0(p36$1, BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32), v9$1[24:16], $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0(p36$2, BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32));
    assume {:do_not_predicate} {:check_id "check_state_11"} {:captureState "check_state_11"} {:sourceloc} {:sourceloc_num 33} true;
    call _CHECK_WRITE_$$A.coerce0.coerce0(p36$2, BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32), v9$2[24:16]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce0"} true;
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)] := (if p36$1 then v9$1[24:16] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)]);
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)] := (if p36$2 then v9$2[24:16] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)]);
    p38$1 := (if p37$1 && base#MKPTR(v14$1) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v14$1) == $arrayId$$A.coerce0.coerce1 else p38$1);
    p38$2 := (if p37$2 && base#MKPTR(v14$2) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v14$2) == $arrayId$$A.coerce0.coerce1 else p38$2);
    p39$1 := (if p37$1 && base#MKPTR(v14$1) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v14$1) != $arrayId$$A.coerce0.coerce1 else p39$1);
    p39$2 := (if p37$2 && base#MKPTR(v14$2) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v14$2) != $arrayId$$A.coerce0.coerce1 else p39$2);
    call _LOG_WRITE_$$A.coerce0.coerce1(p38$1, BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32), v9$1[24:16], $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1(p38$2, BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32));
    assume {:do_not_predicate} {:check_id "check_state_10"} {:captureState "check_state_10"} {:sourceloc} {:sourceloc_num 34} true;
    call _CHECK_WRITE_$$A.coerce0.coerce1(p38$2, BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32), v9$2[24:16]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce1"} true;
    $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)] := (if p38$1 then v9$1[24:16] else $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)]);
    $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)] := (if p38$2 then v9$2[24:16] else $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)]);
    p40$1 := (if p39$1 && base#MKPTR(v14$1) == $arrayId$$A.val then base#MKPTR(v14$1) == $arrayId$$A.val else p40$1);
    p40$2 := (if p39$2 && base#MKPTR(v14$2) == $arrayId$$A.val then base#MKPTR(v14$2) == $arrayId$$A.val else p40$2);
    p41$1 := (if p39$1 && base#MKPTR(v14$1) != $arrayId$$A.val then base#MKPTR(v14$1) != $arrayId$$A.val else p41$1);
    p41$2 := (if p39$2 && base#MKPTR(v14$2) != $arrayId$$A.val then base#MKPTR(v14$2) != $arrayId$$A.val else p41$2);
    $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)] := (if p40$1 then v9$1[24:16] else $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)]);
    $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)] := (if p40$2 then v9$2[24:16] else $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)]);
    assert {:bad_pointer_access} {:sourceloc_num 36} {:thread 1} p41$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 36} {:thread 2} p41$2 ==> false;
    p42$1 := (if base#MKPTR(v14$1) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v14$1) == $arrayId$$A.coerce0.coerce0 else p42$1);
    p42$2 := (if base#MKPTR(v14$2) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v14$2) == $arrayId$$A.coerce0.coerce0 else p42$2);
    p43$1 := (if base#MKPTR(v14$1) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v14$1) != $arrayId$$A.coerce0.coerce0 else p43$1);
    p43$2 := (if base#MKPTR(v14$2) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v14$2) != $arrayId$$A.coerce0.coerce0 else p43$2);
    call _LOG_WRITE_$$A.coerce0.coerce0(p42$1, BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32), v9$1[32:24], $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0(p42$2, BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32));
    assume {:do_not_predicate} {:check_id "check_state_9"} {:captureState "check_state_9"} {:sourceloc} {:sourceloc_num 37} true;
    call _CHECK_WRITE_$$A.coerce0.coerce0(p42$2, BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32), v9$2[32:24]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce0"} true;
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)] := (if p42$1 then v9$1[32:24] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)]);
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)] := (if p42$2 then v9$2[32:24] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)]);
    p44$1 := (if p43$1 && base#MKPTR(v14$1) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v14$1) == $arrayId$$A.coerce0.coerce1 else p44$1);
    p44$2 := (if p43$2 && base#MKPTR(v14$2) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v14$2) == $arrayId$$A.coerce0.coerce1 else p44$2);
    p45$1 := (if p43$1 && base#MKPTR(v14$1) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v14$1) != $arrayId$$A.coerce0.coerce1 else p45$1);
    p45$2 := (if p43$2 && base#MKPTR(v14$2) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v14$2) != $arrayId$$A.coerce0.coerce1 else p45$2);
    call _LOG_WRITE_$$A.coerce0.coerce1(p44$1, BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32), v9$1[32:24], $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1(p44$2, BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32));
    assume {:do_not_predicate} {:check_id "check_state_8"} {:captureState "check_state_8"} {:sourceloc} {:sourceloc_num 38} true;
    call _CHECK_WRITE_$$A.coerce0.coerce1(p44$2, BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32), v9$2[32:24]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce1"} true;
    $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)] := (if p44$1 then v9$1[32:24] else $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)]);
    $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)] := (if p44$2 then v9$2[32:24] else $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)]);
    p46$1 := (if p45$1 && base#MKPTR(v14$1) == $arrayId$$A.val then base#MKPTR(v14$1) == $arrayId$$A.val else p46$1);
    p46$2 := (if p45$2 && base#MKPTR(v14$2) == $arrayId$$A.val then base#MKPTR(v14$2) == $arrayId$$A.val else p46$2);
    p47$1 := (if p45$1 && base#MKPTR(v14$1) != $arrayId$$A.val then base#MKPTR(v14$1) != $arrayId$$A.val else p47$1);
    p47$2 := (if p45$2 && base#MKPTR(v14$2) != $arrayId$$A.val then base#MKPTR(v14$2) != $arrayId$$A.val else p47$2);
    $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)] := (if p46$1 then v9$1[32:24] else $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v14$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)]);
    $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)] := (if p46$2 then v9$2[32:24] else $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v14$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)]);
    assert {:bad_pointer_access} {:sourceloc_num 40} {:thread 1} p47$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 40} {:thread 2} p47$2 ==> false;
    v15$1 := $$A.val$1[4bv32];
    v15$2 := $$A.val$2[4bv32];
    v16$1 := $$A.val$1[5bv32];
    v16$2 := $$A.val$2[5bv32];
    v17$1 := $$A.val$1[6bv32];
    v17$2 := $$A.val$2[6bv32];
    v18$1 := $$A.val$1[7bv32];
    v18$2 := $$A.val$2[7bv32];
    v19$1 := v18$1 ++ v17$1 ++ v16$1 ++ v15$1;
    v19$2 := v18$2 ++ v17$2 ++ v16$2 ++ v15$2;
    p48$1 := (if base#MKPTR(v19$1) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v19$1) == $arrayId$$A.coerce0.coerce0 else p48$1);
    p48$2 := (if base#MKPTR(v19$2) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v19$2) == $arrayId$$A.coerce0.coerce0 else p48$2);
    p49$1 := (if base#MKPTR(v19$1) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v19$1) != $arrayId$$A.coerce0.coerce0 else p49$1);
    p49$2 := (if base#MKPTR(v19$2) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v19$2) != $arrayId$$A.coerce0.coerce0 else p49$2);
    call _LOG_WRITE_$$A.coerce0.coerce0(p48$1, BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), local_id_x$1[8:0], $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0(p48$2, BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)));
    assume {:do_not_predicate} {:check_id "check_state_7"} {:captureState "check_state_7"} {:sourceloc} {:sourceloc_num 45} true;
    call _CHECK_WRITE_$$A.coerce0.coerce0(p48$2, BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), local_id_x$2[8:0]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce0"} true;
    $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))] := (if p48$1 then local_id_x$1[8:0] else $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))]);
    $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))] := (if p48$2 then local_id_x$2[8:0] else $$A.coerce0.coerce0[BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))]);
    p50$1 := (if p49$1 && base#MKPTR(v19$1) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v19$1) == $arrayId$$A.coerce0.coerce1 else p50$1);
    p50$2 := (if p49$2 && base#MKPTR(v19$2) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v19$2) == $arrayId$$A.coerce0.coerce1 else p50$2);
    p51$1 := (if p49$1 && base#MKPTR(v19$1) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v19$1) != $arrayId$$A.coerce0.coerce1 else p51$1);
    p51$2 := (if p49$2 && base#MKPTR(v19$2) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v19$2) != $arrayId$$A.coerce0.coerce1 else p51$2);
    call _LOG_WRITE_$$A.coerce0.coerce1(p50$1, BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), local_id_x$1[8:0], $$A.coerce0.coerce1[BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1(p50$2, BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)));
    assume {:do_not_predicate} {:check_id "check_state_6"} {:captureState "check_state_6"} {:sourceloc} {:sourceloc_num 46} true;
    call _CHECK_WRITE_$$A.coerce0.coerce1(p50$2, BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), local_id_x$2[8:0]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce1"} true;
    $$A.coerce0.coerce1[BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))] := (if p50$1 then local_id_x$1[8:0] else $$A.coerce0.coerce1[BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))]);
    $$A.coerce0.coerce1[BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))] := (if p50$2 then local_id_x$2[8:0] else $$A.coerce0.coerce1[BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))]);
    p52$1 := (if p51$1 && base#MKPTR(v19$1) == $arrayId$$A.val then base#MKPTR(v19$1) == $arrayId$$A.val else p52$1);
    p52$2 := (if p51$2 && base#MKPTR(v19$2) == $arrayId$$A.val then base#MKPTR(v19$2) == $arrayId$$A.val else p52$2);
    p53$1 := (if p51$1 && base#MKPTR(v19$1) != $arrayId$$A.val then base#MKPTR(v19$1) != $arrayId$$A.val else p53$1);
    p53$2 := (if p51$2 && base#MKPTR(v19$2) != $arrayId$$A.val then base#MKPTR(v19$2) != $arrayId$$A.val else p53$2);
    $$A.val$1[BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))] := (if p52$1 then local_id_x$1[8:0] else $$A.val$1[BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32))]);
    $$A.val$2[BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))] := (if p52$2 then local_id_x$2[8:0] else $$A.val$2[BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32))]);
    assert {:bad_pointer_access} {:sourceloc_num 48} {:thread 1} p53$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 48} {:thread 2} p53$2 ==> false;
    p54$1 := (if base#MKPTR(v19$1) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v19$1) == $arrayId$$A.coerce0.coerce0 else p54$1);
    p54$2 := (if base#MKPTR(v19$2) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v19$2) == $arrayId$$A.coerce0.coerce0 else p54$2);
    p55$1 := (if base#MKPTR(v19$1) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v19$1) != $arrayId$$A.coerce0.coerce0 else p55$1);
    p55$2 := (if base#MKPTR(v19$2) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v19$2) != $arrayId$$A.coerce0.coerce0 else p55$2);
    call _LOG_WRITE_$$A.coerce0.coerce0(p54$1, BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32), local_id_x$1[16:8], $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0(p54$2, BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_5"} {:captureState "check_state_5"} {:sourceloc} {:sourceloc_num 49} true;
    call _CHECK_WRITE_$$A.coerce0.coerce0(p54$2, BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32), local_id_x$2[16:8]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce0"} true;
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)] := (if p54$1 then local_id_x$1[16:8] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)]);
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)] := (if p54$2 then local_id_x$2[16:8] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)]);
    p56$1 := (if p55$1 && base#MKPTR(v19$1) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v19$1) == $arrayId$$A.coerce0.coerce1 else p56$1);
    p56$2 := (if p55$2 && base#MKPTR(v19$2) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v19$2) == $arrayId$$A.coerce0.coerce1 else p56$2);
    p57$1 := (if p55$1 && base#MKPTR(v19$1) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v19$1) != $arrayId$$A.coerce0.coerce1 else p57$1);
    p57$2 := (if p55$2 && base#MKPTR(v19$2) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v19$2) != $arrayId$$A.coerce0.coerce1 else p57$2);
    call _LOG_WRITE_$$A.coerce0.coerce1(p56$1, BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32), local_id_x$1[16:8], $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1(p56$2, BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_4"} {:captureState "check_state_4"} {:sourceloc} {:sourceloc_num 50} true;
    call _CHECK_WRITE_$$A.coerce0.coerce1(p56$2, BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32), local_id_x$2[16:8]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce1"} true;
    $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)] := (if p56$1 then local_id_x$1[16:8] else $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)]);
    $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)] := (if p56$2 then local_id_x$2[16:8] else $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)]);
    p58$1 := (if p57$1 && base#MKPTR(v19$1) == $arrayId$$A.val then base#MKPTR(v19$1) == $arrayId$$A.val else p58$1);
    p58$2 := (if p57$2 && base#MKPTR(v19$2) == $arrayId$$A.val then base#MKPTR(v19$2) == $arrayId$$A.val else p58$2);
    p59$1 := (if p57$1 && base#MKPTR(v19$1) != $arrayId$$A.val then base#MKPTR(v19$1) != $arrayId$$A.val else p59$1);
    p59$2 := (if p57$2 && base#MKPTR(v19$2) != $arrayId$$A.val then base#MKPTR(v19$2) != $arrayId$$A.val else p59$2);
    $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)] := (if p58$1 then local_id_x$1[16:8] else $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 1bv32)]);
    $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)] := (if p58$2 then local_id_x$2[16:8] else $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 1bv32)]);
    assert {:bad_pointer_access} {:sourceloc_num 52} {:thread 1} p59$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 52} {:thread 2} p59$2 ==> false;
    p60$1 := (if base#MKPTR(v19$1) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v19$1) == $arrayId$$A.coerce0.coerce0 else p60$1);
    p60$2 := (if base#MKPTR(v19$2) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v19$2) == $arrayId$$A.coerce0.coerce0 else p60$2);
    p61$1 := (if base#MKPTR(v19$1) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v19$1) != $arrayId$$A.coerce0.coerce0 else p61$1);
    p61$2 := (if base#MKPTR(v19$2) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v19$2) != $arrayId$$A.coerce0.coerce0 else p61$2);
    call _LOG_WRITE_$$A.coerce0.coerce0(p60$1, BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32), local_id_x$1[24:16], $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0(p60$2, BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32));
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 53} true;
    call _CHECK_WRITE_$$A.coerce0.coerce0(p60$2, BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32), local_id_x$2[24:16]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce0"} true;
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)] := (if p60$1 then local_id_x$1[24:16] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)]);
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)] := (if p60$2 then local_id_x$2[24:16] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)]);
    p62$1 := (if p61$1 && base#MKPTR(v19$1) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v19$1) == $arrayId$$A.coerce0.coerce1 else p62$1);
    p62$2 := (if p61$2 && base#MKPTR(v19$2) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v19$2) == $arrayId$$A.coerce0.coerce1 else p62$2);
    p63$1 := (if p61$1 && base#MKPTR(v19$1) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v19$1) != $arrayId$$A.coerce0.coerce1 else p63$1);
    p63$2 := (if p61$2 && base#MKPTR(v19$2) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v19$2) != $arrayId$$A.coerce0.coerce1 else p63$2);
    call _LOG_WRITE_$$A.coerce0.coerce1(p62$1, BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32), local_id_x$1[24:16], $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1(p62$2, BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32));
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 54} true;
    call _CHECK_WRITE_$$A.coerce0.coerce1(p62$2, BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32), local_id_x$2[24:16]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce1"} true;
    $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)] := (if p62$1 then local_id_x$1[24:16] else $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)]);
    $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)] := (if p62$2 then local_id_x$2[24:16] else $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)]);
    p64$1 := (if p63$1 && base#MKPTR(v19$1) == $arrayId$$A.val then base#MKPTR(v19$1) == $arrayId$$A.val else p64$1);
    p64$2 := (if p63$2 && base#MKPTR(v19$2) == $arrayId$$A.val then base#MKPTR(v19$2) == $arrayId$$A.val else p64$2);
    p65$1 := (if p63$1 && base#MKPTR(v19$1) != $arrayId$$A.val then base#MKPTR(v19$1) != $arrayId$$A.val else p65$1);
    p65$2 := (if p63$2 && base#MKPTR(v19$2) != $arrayId$$A.val then base#MKPTR(v19$2) != $arrayId$$A.val else p65$2);
    $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)] := (if p64$1 then local_id_x$1[24:16] else $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 2bv32)]);
    $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)] := (if p64$2 then local_id_x$2[24:16] else $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 2bv32)]);
    assert {:bad_pointer_access} {:sourceloc_num 56} {:thread 1} p65$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 56} {:thread 2} p65$2 ==> false;
    p66$1 := (if base#MKPTR(v19$1) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v19$1) == $arrayId$$A.coerce0.coerce0 else p66$1);
    p66$2 := (if base#MKPTR(v19$2) == $arrayId$$A.coerce0.coerce0 then base#MKPTR(v19$2) == $arrayId$$A.coerce0.coerce0 else p66$2);
    p67$1 := (if base#MKPTR(v19$1) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v19$1) != $arrayId$$A.coerce0.coerce0 else p67$1);
    p67$2 := (if base#MKPTR(v19$2) != $arrayId$$A.coerce0.coerce0 then base#MKPTR(v19$2) != $arrayId$$A.coerce0.coerce0 else p67$2);
    call _LOG_WRITE_$$A.coerce0.coerce0(p66$1, BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32), local_id_x$1[32:24], $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce0(p66$2, BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 57} true;
    call _CHECK_WRITE_$$A.coerce0.coerce0(p66$2, BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32), local_id_x$2[32:24]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce0"} true;
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)] := (if p66$1 then local_id_x$1[32:24] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)]);
    $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)] := (if p66$2 then local_id_x$2[32:24] else $$A.coerce0.coerce0[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)]);
    p68$1 := (if p67$1 && base#MKPTR(v19$1) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v19$1) == $arrayId$$A.coerce0.coerce1 else p68$1);
    p68$2 := (if p67$2 && base#MKPTR(v19$2) == $arrayId$$A.coerce0.coerce1 then base#MKPTR(v19$2) == $arrayId$$A.coerce0.coerce1 else p68$2);
    p69$1 := (if p67$1 && base#MKPTR(v19$1) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v19$1) != $arrayId$$A.coerce0.coerce1 else p69$1);
    p69$2 := (if p67$2 && base#MKPTR(v19$2) != $arrayId$$A.coerce0.coerce1 then base#MKPTR(v19$2) != $arrayId$$A.coerce0.coerce1 else p69$2);
    call _LOG_WRITE_$$A.coerce0.coerce1(p68$1, BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32), local_id_x$1[32:24], $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1(p68$2, BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32));
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 58} true;
    call _CHECK_WRITE_$$A.coerce0.coerce1(p68$2, BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32), local_id_x$2[32:24]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A.coerce0.coerce1"} true;
    $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)] := (if p68$1 then local_id_x$1[32:24] else $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)]);
    $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)] := (if p68$2 then local_id_x$2[32:24] else $$A.coerce0.coerce1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)]);
    p70$1 := (if p69$1 && base#MKPTR(v19$1) == $arrayId$$A.val then base#MKPTR(v19$1) == $arrayId$$A.val else p70$1);
    p70$2 := (if p69$2 && base#MKPTR(v19$2) == $arrayId$$A.val then base#MKPTR(v19$2) == $arrayId$$A.val else p70$2);
    p71$1 := (if p69$1 && base#MKPTR(v19$1) != $arrayId$$A.val then base#MKPTR(v19$1) != $arrayId$$A.val else p71$1);
    p71$2 := (if p69$2 && base#MKPTR(v19$2) != $arrayId$$A.val then base#MKPTR(v19$2) != $arrayId$$A.val else p71$2);
    $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)] := (if p70$1 then local_id_x$1[32:24] else $$A.val$1[BV32_ADD(BV32_ADD(offset#MKPTR(v19$1), BV32_MUL(BV32_ADD(local_id_x$1, BV32_MUL(group_size_x, group_id_x$1)), 4bv32)), 3bv32)]);
    $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)] := (if p70$2 then local_id_x$2[32:24] else $$A.val$2[BV32_ADD(BV32_ADD(offset#MKPTR(v19$2), BV32_MUL(BV32_ADD(local_id_x$2, BV32_MUL(group_size_x, group_id_x$2)), 4bv32)), 3bv32)]);
    assert {:bad_pointer_access} {:sourceloc_num 60} {:thread 1} p71$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 60} {:thread 2} p71$2 ==> false;
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

const _WATCHED_VALUE_$$A.coerce0.coerce1: bv8;

procedure {:inline 1} _LOG_READ_$$A.coerce0.coerce1(_P: bool, _offset: bv32, _value: bv8);
  modifies _READ_HAS_OCCURRED_$$A.coerce0.coerce1;

implementation {:inline 1} _LOG_READ_$$A.coerce0.coerce1(_P: bool, _offset: bv32, _value: bv8)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$A.coerce0.coerce1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A.coerce0.coerce1 == _value then true else _READ_HAS_OCCURRED_$$A.coerce0.coerce1);
    return;
}

procedure _CHECK_READ_$$A.coerce0.coerce1(_P: bool, _offset: bv32, _value: bv8);
  requires !(_P && _WRITE_HAS_OCCURRED_$$A.coerce0.coerce1 && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$A.coerce0.coerce1 && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1: bool;

procedure {:inline 1} _LOG_WRITE_$$A.coerce0.coerce1(_P: bool, _offset: bv32, _value: bv8, _value_old: bv8);
  modifies _WRITE_HAS_OCCURRED_$$A.coerce0.coerce1, _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1;

implementation {:inline 1} _LOG_WRITE_$$A.coerce0.coerce1(_P: bool, _offset: bv32, _value: bv8, _value_old: bv8)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$A.coerce0.coerce1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A.coerce0.coerce1 == _value then true else _WRITE_HAS_OCCURRED_$$A.coerce0.coerce1);
    _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A.coerce0.coerce1 == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1);
    return;
}

procedure _CHECK_WRITE_$$A.coerce0.coerce1(_P: bool, _offset: bv32, _value: bv8);
  requires !(_P && _WRITE_HAS_OCCURRED_$$A.coerce0.coerce1 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A.coerce0.coerce1 != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$A.coerce0.coerce1 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A.coerce0.coerce1 != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$A.coerce0.coerce1 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$A.coerce0.coerce1(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$A.coerce0.coerce1;

implementation {:inline 1} _LOG_ATOMIC_$$A.coerce0.coerce1(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$A.coerce0.coerce1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$A.coerce0.coerce1);
    return;
}

procedure _CHECK_ATOMIC_$$A.coerce0.coerce1(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$A.coerce0.coerce1 && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$A.coerce0.coerce1 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1 := (if _P && _WRITE_HAS_OCCURRED_$$A.coerce0.coerce1 && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$A.coerce0.coerce1);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
