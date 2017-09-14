//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "A"} {:global} $$A: [bv32]bv32;

axiom {:array_info "$$A"} {:global} {:elem_width 32} {:source_name "A"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$A: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$A: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$A: bool;

var {:source_name "temp"} $$temp$1: [bv32]bv32;

var {:source_name "temp"} $$temp$2: [bv32]bv32;

axiom {:array_info "$$temp"} {:elem_width 32} {:source_name "temp"} {:source_elem_width 32} {:source_dimensions "32"} true;

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

function {:builtin "bvsub"} BV32_SUB(bv32, bv32) : bv32;

function {:builtin "bvudiv"} BV32_UDIV(bv32, bv32) : bv32;

function {:builtin "bvuge"} BV32_UGE(bv32, bv32) : bool;

function {:builtin "bvurem"} BV32_UREM(bv32, bv32) : bv32;

procedure {:source_name "scan"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$A && !_WRITE_HAS_OCCURRED_$$A && !_ATOMIC_HAS_OCCURRED_$$A;
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
  modifies _READ_HAS_OCCURRED_$$A, _WRITE_HAS_OCCURRED_$$A, _WRITE_READ_BENIGN_FLAG_$$A, _WRITE_READ_BENIGN_FLAG_$$A, $$A, _TRACKING, _TRACKING, _TRACKING;

implementation {:source_name "scan"} ULTIMATE.start()
{
  var v10$1: bool;
  var v10$2: bool;
  var v0$1: bv32;
  var v0$2: bv32;
  var v1$1: bool;
  var v1$2: bool;
  var v2$1: bv32;
  var v2$2: bv32;
  var v3$1: bv32;
  var v3$2: bv32;
  var v4$1: bool;
  var v4$2: bool;
  var v5$1: bv32;
  var v5$2: bv32;
  var v9$1: bv32;
  var v9$2: bv32;
  var v6$1: bv32;
  var v6$2: bv32;
  var v7$1: bool;
  var v7$2: bool;
  var v8$1: bv32;
  var v8$2: bv32;
  var v11$1: bv32;
  var v11$2: bv32;
  var v12$1: bv32;
  var v12$2: bv32;
  var v13$1: bool;
  var v13$2: bool;
  var v14$1: bv32;
  var v14$2: bv32;
  var v15$1: bv32;
  var v15$2: bv32;
  var v16$1: bool;
  var v16$2: bool;
  var v17$1: bv32;
  var v17$2: bv32;
  var v18$1: bool;
  var v18$2: bool;
  var v19$1: bv32;
  var v19$2: bv32;
  var v20$1: bool;
  var v20$2: bool;
  var v21$1: bv32;
  var v21$2: bv32;
  var v22$1: bv32;
  var v22$2: bv32;
  var v23$1: bool;
  var v23$2: bool;
  var v24$1: bv32;
  var v24$2: bv32;
  var v25$1: bv32;
  var v25$2: bv32;
  var v26$1: bool;
  var v26$2: bool;
  var v27$1: bv32;
  var v27$2: bv32;
  var v28$1: bv32;
  var v28$2: bv32;
  var v29$1: bool;
  var v29$2: bool;
  var v30$1: bv32;
  var v30$2: bv32;
  var v31$1: bv32;
  var v31$2: bv32;
  var v32$1: bool;
  var v32$2: bool;
  var v33$1: bv32;
  var v33$2: bv32;
  var v34$1: bv32;
  var v34$2: bv32;
  var v35$1: bv32;
  var v35$2: bv32;
  var v36$1: bv32;
  var v36$2: bv32;
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

  __partitioned_block_$entry_0:
    v0$1 := BV32_UREM(local_id_x$1, 32bv32);
    v0$2 := BV32_UREM(local_id_x$2, 32bv32);
    v1$1 := BV32_UGE(v0$1, 1bv32);
    v1$2 := BV32_UGE(v0$2, 1bv32);
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
    p0$1 := (if v1$1 then v1$1 else p0$1);
    p0$2 := (if v1$2 then v1$2 else p0$2);
    call _PRE_WARP_SYNC_$$A_READ(p0$1, p0$2);
    call _LOG_READ_$$A(p0$1, BV32_SUB(local_id_x$1, 1bv32), $$A[BV32_SUB(local_id_x$1, 1bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_15"} {:captureState "check_state_15"} {:sourceloc} {:sourceloc_num 2} true;
    call _CHECK_READ_$$A(p0$2, BV32_SUB(local_id_x$2, 1bv32), $$A[BV32_SUB(local_id_x$2, 1bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p0$1, p0$2);
    v2$1 := (if p0$1 then $$A[BV32_SUB(local_id_x$1, 1bv32)] else v2$1);
    v2$2 := (if p0$2 then $$A[BV32_SUB(local_id_x$2, 1bv32)] else v2$2);
    call _PRE_WARP_SYNC_$$A_READ(p0$1, p0$2);
    call _LOG_READ_$$A(p0$1, local_id_x$1, $$A[local_id_x$1]);
    assume {:do_not_predicate} {:check_id "check_state_16"} {:captureState "check_state_16"} {:sourceloc} {:sourceloc_num 3} true;
    call _CHECK_READ_$$A(p0$2, local_id_x$2, $$A[local_id_x$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p0$1, p0$2);
    v3$1 := (if p0$1 then $$A[local_id_x$1] else v3$1);
    v3$2 := (if p0$2 then $$A[local_id_x$2] else v3$2);
    call _PRE_WARP_SYNC_$$A_WRITE(p0$1, p0$2);
    call _LOG_WRITE_$$A(p0$1, local_id_x$1, BV32_ADD(v2$1, v3$1), $$A[local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(p0$2, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_17"} {:captureState "check_state_17"} {:sourceloc} {:sourceloc_num 4} true;
    call _CHECK_WRITE_$$A(p0$2, local_id_x$2, BV32_ADD(v2$2, v3$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A"} true;
    call _POST_WARP_SYNC_$$A_WRITE(p0$1, p0$2);
    $$A[local_id_x$1] := (if p0$1 then BV32_ADD(v2$1, v3$1) else $$A[local_id_x$1]);
    $$A[local_id_x$2] := (if p0$2 then BV32_ADD(v2$2, v3$2) else $$A[local_id_x$2]);
    v4$1 := BV32_UGE(v0$1, 2bv32);
    v4$2 := BV32_UGE(v0$2, 2bv32);
    p2$1 := (if v4$1 then v4$1 else p2$1);
    p2$2 := (if v4$2 then v4$2 else p2$2);
    call _PRE_WARP_SYNC_$$A_READ(p2$1, p2$2);
    call _LOG_READ_$$A(p2$1, BV32_SUB(local_id_x$1, 2bv32), $$A[BV32_SUB(local_id_x$1, 2bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_12"} {:captureState "check_state_12"} {:sourceloc} {:sourceloc_num 7} true;
    call _CHECK_READ_$$A(p2$2, BV32_SUB(local_id_x$2, 2bv32), $$A[BV32_SUB(local_id_x$2, 2bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p2$1, p2$2);
    v5$1 := (if p2$1 then $$A[BV32_SUB(local_id_x$1, 2bv32)] else v5$1);
    v5$2 := (if p2$2 then $$A[BV32_SUB(local_id_x$2, 2bv32)] else v5$2);
    call _PRE_WARP_SYNC_$$A_READ(p2$1, p2$2);
    call _LOG_READ_$$A(p2$1, local_id_x$1, $$A[local_id_x$1]);
    assume {:do_not_predicate} {:check_id "check_state_13"} {:captureState "check_state_13"} {:sourceloc} {:sourceloc_num 8} true;
    call _CHECK_READ_$$A(p2$2, local_id_x$2, $$A[local_id_x$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p2$1, p2$2);
    v6$1 := (if p2$1 then $$A[local_id_x$1] else v6$1);
    v6$2 := (if p2$2 then $$A[local_id_x$2] else v6$2);
    call _PRE_WARP_SYNC_$$A_WRITE(p2$1, p2$2);
    call _LOG_WRITE_$$A(p2$1, local_id_x$1, BV32_ADD(v5$1, v6$1), $$A[local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(p2$2, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_14"} {:captureState "check_state_14"} {:sourceloc} {:sourceloc_num 9} true;
    call _CHECK_WRITE_$$A(p2$2, local_id_x$2, BV32_ADD(v5$2, v6$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A"} true;
    call _POST_WARP_SYNC_$$A_WRITE(p2$1, p2$2);
    $$A[local_id_x$1] := (if p2$1 then BV32_ADD(v5$1, v6$1) else $$A[local_id_x$1]);
    $$A[local_id_x$2] := (if p2$2 then BV32_ADD(v5$2, v6$2) else $$A[local_id_x$2]);
    v7$1 := BV32_UGE(v0$1, 4bv32);
    v7$2 := BV32_UGE(v0$2, 4bv32);
    p4$1 := (if v7$1 then v7$1 else p4$1);
    p4$2 := (if v7$2 then v7$2 else p4$2);
    call _PRE_WARP_SYNC_$$A_READ(p4$1, p4$2);
    call _LOG_READ_$$A(p4$1, BV32_SUB(local_id_x$1, 4bv32), $$A[BV32_SUB(local_id_x$1, 4bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_9"} {:captureState "check_state_9"} {:sourceloc} {:sourceloc_num 12} true;
    call _CHECK_READ_$$A(p4$2, BV32_SUB(local_id_x$2, 4bv32), $$A[BV32_SUB(local_id_x$2, 4bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p4$1, p4$2);
    v8$1 := (if p4$1 then $$A[BV32_SUB(local_id_x$1, 4bv32)] else v8$1);
    v8$2 := (if p4$2 then $$A[BV32_SUB(local_id_x$2, 4bv32)] else v8$2);
    call _PRE_WARP_SYNC_$$A_READ(p4$1, p4$2);
    call _LOG_READ_$$A(p4$1, local_id_x$1, $$A[local_id_x$1]);
    assume {:do_not_predicate} {:check_id "check_state_10"} {:captureState "check_state_10"} {:sourceloc} {:sourceloc_num 13} true;
    call _CHECK_READ_$$A(p4$2, local_id_x$2, $$A[local_id_x$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p4$1, p4$2);
    v9$1 := (if p4$1 then $$A[local_id_x$1] else v9$1);
    v9$2 := (if p4$2 then $$A[local_id_x$2] else v9$2);
    call _PRE_WARP_SYNC_$$A_WRITE(p4$1, p4$2);
    call _LOG_WRITE_$$A(p4$1, local_id_x$1, BV32_ADD(v8$1, v9$1), $$A[local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(p4$2, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_11"} {:captureState "check_state_11"} {:sourceloc} {:sourceloc_num 14} true;
    call _CHECK_WRITE_$$A(p4$2, local_id_x$2, BV32_ADD(v8$2, v9$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A"} true;
    call _POST_WARP_SYNC_$$A_WRITE(p4$1, p4$2);
    $$A[local_id_x$1] := (if p4$1 then BV32_ADD(v8$1, v9$1) else $$A[local_id_x$1]);
    $$A[local_id_x$2] := (if p4$2 then BV32_ADD(v8$2, v9$2) else $$A[local_id_x$2]);
    v10$1 := BV32_UGE(v0$1, 8bv32);
    v10$2 := BV32_UGE(v0$2, 8bv32);
    p6$1 := (if v10$1 then v10$1 else p6$1);
    p6$2 := (if v10$2 then v10$2 else p6$2);
    call _PRE_WARP_SYNC_$$A_READ(p6$1, p6$2);
    call _LOG_READ_$$A(p6$1, BV32_SUB(local_id_x$1, 8bv32), $$A[BV32_SUB(local_id_x$1, 8bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_6"} {:captureState "check_state_6"} {:sourceloc} {:sourceloc_num 17} true;
    call _CHECK_READ_$$A(p6$2, BV32_SUB(local_id_x$2, 8bv32), $$A[BV32_SUB(local_id_x$2, 8bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p6$1, p6$2);
    v11$1 := (if p6$1 then $$A[BV32_SUB(local_id_x$1, 8bv32)] else v11$1);
    v11$2 := (if p6$2 then $$A[BV32_SUB(local_id_x$2, 8bv32)] else v11$2);
    call _PRE_WARP_SYNC_$$A_READ(p6$1, p6$2);
    call _LOG_READ_$$A(p6$1, local_id_x$1, $$A[local_id_x$1]);
    assume {:do_not_predicate} {:check_id "check_state_7"} {:captureState "check_state_7"} {:sourceloc} {:sourceloc_num 18} true;
    call _CHECK_READ_$$A(p6$2, local_id_x$2, $$A[local_id_x$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p6$1, p6$2);
    v12$1 := (if p6$1 then $$A[local_id_x$1] else v12$1);
    v12$2 := (if p6$2 then $$A[local_id_x$2] else v12$2);
    call _PRE_WARP_SYNC_$$A_WRITE(p6$1, p6$2);
    call _LOG_WRITE_$$A(p6$1, local_id_x$1, BV32_ADD(v11$1, v12$1), $$A[local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(p6$2, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_8"} {:captureState "check_state_8"} {:sourceloc} {:sourceloc_num 19} true;
    call _CHECK_WRITE_$$A(p6$2, local_id_x$2, BV32_ADD(v11$2, v12$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A"} true;
    call _POST_WARP_SYNC_$$A_WRITE(p6$1, p6$2);
    $$A[local_id_x$1] := (if p6$1 then BV32_ADD(v11$1, v12$1) else $$A[local_id_x$1]);
    $$A[local_id_x$2] := (if p6$2 then BV32_ADD(v11$2, v12$2) else $$A[local_id_x$2]);
    v13$1 := BV32_UGE(v0$1, 16bv32);
    v13$2 := BV32_UGE(v0$2, 16bv32);
    p8$1 := (if v13$1 then v13$1 else p8$1);
    p8$2 := (if v13$2 then v13$2 else p8$2);
    call _PRE_WARP_SYNC_$$A_READ(p8$1, p8$2);
    call _LOG_READ_$$A(p8$1, BV32_SUB(local_id_x$1, 16bv32), $$A[BV32_SUB(local_id_x$1, 16bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 22} true;
    call _CHECK_READ_$$A(p8$2, BV32_SUB(local_id_x$2, 16bv32), $$A[BV32_SUB(local_id_x$2, 16bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p8$1, p8$2);
    v14$1 := (if p8$1 then $$A[BV32_SUB(local_id_x$1, 16bv32)] else v14$1);
    v14$2 := (if p8$2 then $$A[BV32_SUB(local_id_x$2, 16bv32)] else v14$2);
    call _PRE_WARP_SYNC_$$A_READ(p8$1, p8$2);
    call _LOG_READ_$$A(p8$1, local_id_x$1, $$A[local_id_x$1]);
    assume {:do_not_predicate} {:check_id "check_state_4"} {:captureState "check_state_4"} {:sourceloc} {:sourceloc_num 23} true;
    call _CHECK_READ_$$A(p8$2, local_id_x$2, $$A[local_id_x$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p8$1, p8$2);
    v15$1 := (if p8$1 then $$A[local_id_x$1] else v15$1);
    v15$2 := (if p8$2 then $$A[local_id_x$2] else v15$2);
    call _PRE_WARP_SYNC_$$A_WRITE(p8$1, p8$2);
    call _LOG_WRITE_$$A(p8$1, local_id_x$1, BV32_ADD(v14$1, v15$1), $$A[local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(p8$2, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_5"} {:captureState "check_state_5"} {:sourceloc} {:sourceloc_num 24} true;
    call _CHECK_WRITE_$$A(p8$2, local_id_x$2, BV32_ADD(v14$2, v15$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A"} true;
    call _POST_WARP_SYNC_$$A_WRITE(p8$1, p8$2);
    $$A[local_id_x$1] := (if p8$1 then BV32_ADD(v14$1, v15$1) else $$A[local_id_x$1]);
    $$A[local_id_x$2] := (if p8$2 then BV32_ADD(v14$2, v15$2) else $$A[local_id_x$2]);
    goto __partitioned_block_$entry_1;

  __partitioned_block_$entry_1:
    call $bugle_barrier_duplicated_0(1bv1, 1bv1);
    v16$1 := BV32_UREM(local_id_x$1, 32bv32) == 31bv32;
    v16$2 := BV32_UREM(local_id_x$2, 32bv32) == 31bv32;
    p10$1 := (if v16$1 then v16$1 else p10$1);
    p10$2 := (if v16$2 then v16$2 else p10$2);
    call _PRE_WARP_SYNC_$$A_READ(p10$1, p10$2);
    call _LOG_READ_$$A(p10$1, local_id_x$1, $$A[local_id_x$1]);
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 28} true;
    call _CHECK_READ_$$A(p10$2, local_id_x$2, $$A[local_id_x$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p10$1, p10$2);
    v17$1 := (if p10$1 then $$A[local_id_x$1] else v17$1);
    v17$2 := (if p10$2 then $$A[local_id_x$2] else v17$2);
    $$temp$1[BV32_UDIV(local_id_x$1, 32bv32)] := (if p10$1 then v17$1 else $$temp$1[BV32_UDIV(local_id_x$1, 32bv32)]);
    $$temp$2[BV32_UDIV(local_id_x$2, 32bv32)] := (if p10$2 then v17$2 else $$temp$2[BV32_UDIV(local_id_x$2, 32bv32)]);
    goto __partitioned_block_$entry_2;

  __partitioned_block_$entry_2:
    call $bugle_barrier_duplicated_1(1bv1, 1bv1);
    v18$1 := BV32_UDIV(local_id_x$1, 32bv32) == 0bv32;
    v18$2 := BV32_UDIV(local_id_x$2, 32bv32) == 0bv32;
    p12$1 := (if v18$1 then v18$1 else p12$1);
    p12$2 := (if v18$2 then v18$2 else p12$2);
    v19$1 := (if p12$1 then BV32_UREM(local_id_x$1, 32bv32) else v19$1);
    v19$2 := (if p12$2 then BV32_UREM(local_id_x$2, 32bv32) else v19$2);
    v20$1 := (if p12$1 then BV32_UGE(v19$1, 1bv32) else v20$1);
    v20$2 := (if p12$2 then BV32_UGE(v19$2, 1bv32) else v20$2);
    p13$1 := (if p12$1 && v20$1 then v20$1 else p13$1);
    p13$2 := (if p12$2 && v20$2 then v20$2 else p13$2);
    v21$1 := (if p13$1 then $$temp$1[BV32_SUB(local_id_x$1, 1bv32)] else v21$1);
    v21$2 := (if p13$2 then $$temp$2[BV32_SUB(local_id_x$2, 1bv32)] else v21$2);
    v22$1 := (if p13$1 then $$temp$1[local_id_x$1] else v22$1);
    v22$2 := (if p13$2 then $$temp$2[local_id_x$2] else v22$2);
    $$temp$1[local_id_x$1] := (if p13$1 then BV32_ADD(v21$1, v22$1) else $$temp$1[local_id_x$1]);
    $$temp$2[local_id_x$2] := (if p13$2 then BV32_ADD(v21$2, v22$2) else $$temp$2[local_id_x$2]);
    v23$1 := (if p12$1 then BV32_UGE(v19$1, 2bv32) else v23$1);
    v23$2 := (if p12$2 then BV32_UGE(v19$2, 2bv32) else v23$2);
    p15$1 := (if p12$1 && v23$1 then v23$1 else p15$1);
    p15$2 := (if p12$2 && v23$2 then v23$2 else p15$2);
    v24$1 := (if p15$1 then $$temp$1[BV32_SUB(local_id_x$1, 2bv32)] else v24$1);
    v24$2 := (if p15$2 then $$temp$2[BV32_SUB(local_id_x$2, 2bv32)] else v24$2);
    v25$1 := (if p15$1 then $$temp$1[local_id_x$1] else v25$1);
    v25$2 := (if p15$2 then $$temp$2[local_id_x$2] else v25$2);
    $$temp$1[local_id_x$1] := (if p15$1 then BV32_ADD(v24$1, v25$1) else $$temp$1[local_id_x$1]);
    $$temp$2[local_id_x$2] := (if p15$2 then BV32_ADD(v24$2, v25$2) else $$temp$2[local_id_x$2]);
    v26$1 := (if p12$1 then BV32_UGE(v19$1, 4bv32) else v26$1);
    v26$2 := (if p12$2 then BV32_UGE(v19$2, 4bv32) else v26$2);
    p17$1 := (if p12$1 && v26$1 then v26$1 else p17$1);
    p17$2 := (if p12$2 && v26$2 then v26$2 else p17$2);
    v27$1 := (if p17$1 then $$temp$1[BV32_SUB(local_id_x$1, 4bv32)] else v27$1);
    v27$2 := (if p17$2 then $$temp$2[BV32_SUB(local_id_x$2, 4bv32)] else v27$2);
    v28$1 := (if p17$1 then $$temp$1[local_id_x$1] else v28$1);
    v28$2 := (if p17$2 then $$temp$2[local_id_x$2] else v28$2);
    $$temp$1[local_id_x$1] := (if p17$1 then BV32_ADD(v27$1, v28$1) else $$temp$1[local_id_x$1]);
    $$temp$2[local_id_x$2] := (if p17$2 then BV32_ADD(v27$2, v28$2) else $$temp$2[local_id_x$2]);
    v29$1 := (if p12$1 then BV32_UGE(v19$1, 8bv32) else v29$1);
    v29$2 := (if p12$2 then BV32_UGE(v19$2, 8bv32) else v29$2);
    p19$1 := (if p12$1 && v29$1 then v29$1 else p19$1);
    p19$2 := (if p12$2 && v29$2 then v29$2 else p19$2);
    v30$1 := (if p19$1 then $$temp$1[BV32_SUB(local_id_x$1, 8bv32)] else v30$1);
    v30$2 := (if p19$2 then $$temp$2[BV32_SUB(local_id_x$2, 8bv32)] else v30$2);
    v31$1 := (if p19$1 then $$temp$1[local_id_x$1] else v31$1);
    v31$2 := (if p19$2 then $$temp$2[local_id_x$2] else v31$2);
    $$temp$1[local_id_x$1] := (if p19$1 then BV32_ADD(v30$1, v31$1) else $$temp$1[local_id_x$1]);
    $$temp$2[local_id_x$2] := (if p19$2 then BV32_ADD(v30$2, v31$2) else $$temp$2[local_id_x$2]);
    v32$1 := (if p12$1 then BV32_UGE(v19$1, 16bv32) else v32$1);
    v32$2 := (if p12$2 then BV32_UGE(v19$2, 16bv32) else v32$2);
    p21$1 := (if p12$1 && v32$1 then v32$1 else p21$1);
    p21$2 := (if p12$2 && v32$2 then v32$2 else p21$2);
    v33$1 := (if p21$1 then $$temp$1[BV32_SUB(local_id_x$1, 16bv32)] else v33$1);
    v33$2 := (if p21$2 then $$temp$2[BV32_SUB(local_id_x$2, 16bv32)] else v33$2);
    v34$1 := (if p21$1 then $$temp$1[local_id_x$1] else v34$1);
    v34$2 := (if p21$2 then $$temp$2[local_id_x$2] else v34$2);
    $$temp$1[local_id_x$1] := (if p21$1 then BV32_ADD(v33$1, v34$1) else $$temp$1[local_id_x$1]);
    $$temp$2[local_id_x$2] := (if p21$2 then BV32_ADD(v33$2, v34$2) else $$temp$2[local_id_x$2]);
    goto __partitioned_block_$entry_3;

  __partitioned_block_$entry_3:
    call $bugle_barrier_duplicated_2(1bv1, 1bv1);
    v35$1 := $$temp$1[BV32_UDIV(local_id_x$1, 32bv32)];
    v35$2 := $$temp$2[BV32_UDIV(local_id_x$2, 32bv32)];
    call _PRE_WARP_SYNC_$$A_READ(true, true);
    call _LOG_READ_$$A(true, local_id_x$1, $$A[local_id_x$1]);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 61} true;
    call _CHECK_READ_$$A(true, local_id_x$2, $$A[local_id_x$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(true, true);
    v36$1 := $$A[local_id_x$1];
    v36$2 := $$A[local_id_x$2];
    call _PRE_WARP_SYNC_$$A_WRITE(true, true);
    call _LOG_WRITE_$$A(true, local_id_x$1, BV32_ADD(v36$1, v35$1), $$A[local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(true, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 62} true;
    call _CHECK_WRITE_$$A(true, local_id_x$2, BV32_ADD(v36$2, v35$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A"} true;
    call _POST_WARP_SYNC_$$A_WRITE(true, true);
    $$A[local_id_x$1] := BV32_ADD(v36$1, v35$1);
    $$A[local_id_x$2] := BV32_ADD(v36$2, v35$2);
    return;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 512bv32 then 1bv1 else 0bv1) != 0bv1;

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

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_0($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 1bv1;
  modifies $$A, _TRACKING;

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_1($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 1bv1;
  modifies $$A, _TRACKING;

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_2($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 1bv1;
  modifies $$A, _TRACKING;

procedure {:inline 1} _PRE_WARP_SYNC_$$A_READ(_P$1: bool, _P$2: bool);

procedure {:inline 1} _POST_WARP_SYNC_$$A_READ(_P$1: bool, _P$2: bool);

procedure {:inline 1} _PRE_WARP_SYNC_$$A_WRITE(_P$1: bool, _P$2: bool);

procedure {:inline 1} _POST_WARP_SYNC_$$A_WRITE(_P$1: bool, _P$2: bool);

const _WATCHED_VALUE_$$A: bv32;

procedure {:inline 1} _LOG_READ_$$A(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$A;

implementation {:inline 1} _LOG_READ_$$A(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$A := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A == _value then true else _READ_HAS_OCCURRED_$$A);
    return;
}

procedure _CHECK_READ_$$A(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$A);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$A: bool;

procedure {:inline 1} _LOG_WRITE_$$A(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$A, _WRITE_READ_BENIGN_FLAG_$$A;

implementation {:inline 1} _LOG_WRITE_$$A(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$A := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A == _value then true else _WRITE_HAS_OCCURRED_$$A);
    _WRITE_READ_BENIGN_FLAG_$$A := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$A);
    return;
}

procedure _CHECK_WRITE_$$A(_P: bool, _offset: bv32, _value: bv32);
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

var _TRACKING: bool;

implementation {:inline 1} $bugle_barrier_duplicated_0($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon4_Then, anon4_Else;

  anon4_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$A;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$A;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$A;
    goto anon1;

  anon1:
    goto anon5_Then, anon5_Else;

  anon5_Else:
    assume {:partition} !(group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1));
    goto anon3;

  anon3:
    havoc _TRACKING;
    return;

  anon5_Then:
    assume {:partition} group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1);
    havoc $$A;
    goto anon3;

  anon4_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

implementation {:inline 1} $bugle_barrier_duplicated_1($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon4_Then, anon4_Else;

  anon4_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$A;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$A;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$A;
    goto anon1;

  anon1:
    goto anon5_Then, anon5_Else;

  anon5_Else:
    assume {:partition} !(group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1));
    goto anon3;

  anon3:
    havoc _TRACKING;
    return;

  anon5_Then:
    assume {:partition} group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1);
    havoc $$A;
    goto anon3;

  anon4_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

implementation {:inline 1} $bugle_barrier_duplicated_2($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon4_Then, anon4_Else;

  anon4_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$A;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$A;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$A;
    goto anon1;

  anon1:
    goto anon5_Then, anon5_Else;

  anon5_Else:
    assume {:partition} !(group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1));
    goto anon3;

  anon3:
    havoc _TRACKING;
    return;

  anon5_Then:
    assume {:partition} group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1);
    havoc $$A;
    goto anon3;

  anon4_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

function {:builtin "bvsdiv"} BV32_DIV(bv32, bv32) : bv32;

implementation {:inline 1} _PRE_WARP_SYNC_$$A_READ(_P$1: bool, _P$2: bool)
{

  entry:
    goto anon0_Then, anon0_Else;

  anon0_Then:
    assume {:partition} _P$1 == _P$2 && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && BV32_DIV(BV32_ADD(local_id_x$1, BV32_ADD(BV32_MUL(local_id_y$1, group_size_x), BV32_MUL(local_id_z$1, BV32_MUL(group_size_x, group_size_y)))), 32bv32) == BV32_DIV(BV32_ADD(local_id_x$2, BV32_ADD(BV32_MUL(local_id_y$2, group_size_x), BV32_MUL(local_id_z$2, BV32_MUL(group_size_x, group_size_y)))), 32bv32);
    goto reset_warps;

  reset_warps:
    assume !_WRITE_HAS_OCCURRED_$$A;
    assume !_ATOMIC_HAS_OCCURRED_$$A;
    return;

  anon0_Else:
    assume {:partition} !(_P$1 == _P$2 && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && BV32_DIV(BV32_ADD(local_id_x$1, BV32_ADD(BV32_MUL(local_id_y$1, group_size_x), BV32_MUL(local_id_z$1, BV32_MUL(group_size_x, group_size_y)))), 32bv32) == BV32_DIV(BV32_ADD(local_id_x$2, BV32_ADD(BV32_MUL(local_id_y$2, group_size_x), BV32_MUL(local_id_z$2, BV32_MUL(group_size_x, group_size_y)))), 32bv32));
    return;
}

implementation {:inline 1} _POST_WARP_SYNC_$$A_READ(_P$1: bool, _P$2: bool)
{

  entry:
    goto anon0_Then, anon0_Else;

  anon0_Then:
    assume {:partition} _P$1 == _P$2 && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && BV32_DIV(BV32_ADD(local_id_x$1, BV32_ADD(BV32_MUL(local_id_y$1, group_size_x), BV32_MUL(local_id_z$1, BV32_MUL(group_size_x, group_size_y)))), 32bv32) == BV32_DIV(BV32_ADD(local_id_x$2, BV32_ADD(BV32_MUL(local_id_y$2, group_size_x), BV32_MUL(local_id_z$2, BV32_MUL(group_size_x, group_size_y)))), 32bv32);
    goto reset_warps;

  reset_warps:
    assume !_READ_HAS_OCCURRED_$$A;
    return;

  anon0_Else:
    assume {:partition} !(_P$1 == _P$2 && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && BV32_DIV(BV32_ADD(local_id_x$1, BV32_ADD(BV32_MUL(local_id_y$1, group_size_x), BV32_MUL(local_id_z$1, BV32_MUL(group_size_x, group_size_y)))), 32bv32) == BV32_DIV(BV32_ADD(local_id_x$2, BV32_ADD(BV32_MUL(local_id_y$2, group_size_x), BV32_MUL(local_id_z$2, BV32_MUL(group_size_x, group_size_y)))), 32bv32));
    return;
}

implementation {:inline 1} _PRE_WARP_SYNC_$$A_WRITE(_P$1: bool, _P$2: bool)
{

  entry:
    goto anon1_Then, anon1_Else;

  anon1_Then:
    assume {:partition} _P$1 == _P$2 && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && BV32_DIV(BV32_ADD(local_id_x$1, BV32_ADD(BV32_MUL(local_id_y$1, group_size_x), BV32_MUL(local_id_z$1, BV32_MUL(group_size_x, group_size_y)))), 32bv32) == BV32_DIV(BV32_ADD(local_id_x$2, BV32_ADD(BV32_MUL(local_id_y$2, group_size_x), BV32_MUL(local_id_z$2, BV32_MUL(group_size_x, group_size_y)))), 32bv32);
    goto reset_warps;

  reset_warps:
    assume !_READ_HAS_OCCURRED_$$A;
    assume !_WRITE_HAS_OCCURRED_$$A;
    assume !_ATOMIC_HAS_OCCURRED_$$A;
    goto anon0;

  anon0:
    havoc $$A;
    return;

  anon1_Else:
    assume {:partition} !(_P$1 == _P$2 && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && BV32_DIV(BV32_ADD(local_id_x$1, BV32_ADD(BV32_MUL(local_id_y$1, group_size_x), BV32_MUL(local_id_z$1, BV32_MUL(group_size_x, group_size_y)))), 32bv32) == BV32_DIV(BV32_ADD(local_id_x$2, BV32_ADD(BV32_MUL(local_id_y$2, group_size_x), BV32_MUL(local_id_z$2, BV32_MUL(group_size_x, group_size_y)))), 32bv32));
    return;
}

implementation {:inline 1} _POST_WARP_SYNC_$$A_WRITE(_P$1: bool, _P$2: bool)
{

  entry:
    goto anon1_Then, anon1_Else;

  anon1_Then:
    assume {:partition} _P$1 == _P$2 && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && BV32_DIV(BV32_ADD(local_id_x$1, BV32_ADD(BV32_MUL(local_id_y$1, group_size_x), BV32_MUL(local_id_z$1, BV32_MUL(group_size_x, group_size_y)))), 32bv32) == BV32_DIV(BV32_ADD(local_id_x$2, BV32_ADD(BV32_MUL(local_id_y$2, group_size_x), BV32_MUL(local_id_z$2, BV32_MUL(group_size_x, group_size_y)))), 32bv32);
    goto reset_warps;

  reset_warps:
    assume !_WRITE_HAS_OCCURRED_$$A;
    goto anon0;

  anon0:
    havoc $$A;
    return;

  anon1_Else:
    assume {:partition} !(_P$1 == _P$2 && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && BV32_DIV(BV32_ADD(local_id_x$1, BV32_ADD(BV32_MUL(local_id_y$1, group_size_x), BV32_MUL(local_id_z$1, BV32_MUL(group_size_x, group_size_y)))), 32bv32) == BV32_DIV(BV32_ADD(local_id_x$2, BV32_ADD(BV32_MUL(local_id_y$2, group_size_x), BV32_MUL(local_id_z$2, BV32_MUL(group_size_x, group_size_y)))), 32bv32));
    return;
}

