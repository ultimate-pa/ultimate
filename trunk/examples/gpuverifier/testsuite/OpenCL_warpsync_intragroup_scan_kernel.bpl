//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "A"} {:group_shared} $$A: [bv1][bv32]bv32;

axiom {:array_info "$$A"} {:group_shared} {:elem_width 32} {:source_name "A"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$A: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$A: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$A: bool;

var {:source_name "temp"} {:group_shared} $$scan.temp: [bv1][bv32]bv32;

axiom {:array_info "$$scan.temp"} {:group_shared} {:elem_width 32} {:source_name "temp"} {:source_elem_width 32} {:source_dimensions "32"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$scan.temp: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$scan.temp: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$scan.temp: bool;

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

function {:builtin "bvsub"} BV32_SUB(bv32, bv32) : bv32;

function {:builtin "bvudiv"} BV32_UDIV(bv32, bv32) : bv32;

function {:builtin "bvuge"} BV32_UGE(bv32, bv32) : bool;

function {:builtin "bvurem"} BV32_UREM(bv32, bv32) : bv32;

procedure {:source_name "scan"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$A && !_WRITE_HAS_OCCURRED_$$A && !_ATOMIC_HAS_OCCURRED_$$A;
  requires !_READ_HAS_OCCURRED_$$scan.temp && !_WRITE_HAS_OCCURRED_$$scan.temp && !_ATOMIC_HAS_OCCURRED_$$scan.temp;
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
  modifies $$A, $$scan.temp, _READ_HAS_OCCURRED_$$A, _WRITE_HAS_OCCURRED_$$A, _WRITE_READ_BENIGN_FLAG_$$A, _WRITE_READ_BENIGN_FLAG_$$A, _TRACKING, _WRITE_HAS_OCCURRED_$$scan.temp, _WRITE_READ_BENIGN_FLAG_$$scan.temp, _WRITE_READ_BENIGN_FLAG_$$scan.temp, _TRACKING, _READ_HAS_OCCURRED_$$scan.temp, _TRACKING;

implementation {:source_name "scan"} ULTIMATE.start()
{
  var v0$1: bv32;
  var v0$2: bv32;
  var v1$1: bv32;
  var v1$2: bv32;
  var v2$1: bv32;
  var v2$2: bv32;
  var v3$1: bool;
  var v3$2: bool;
  var v4$1: bv32;
  var v4$2: bv32;
  var v5$1: bv32;
  var v5$2: bv32;
  var v6$1: bool;
  var v6$2: bool;
  var v7$1: bv32;
  var v7$2: bv32;
  var v8$1: bv32;
  var v8$2: bv32;
  var v9$1: bool;
  var v9$2: bool;
  var v10$1: bv32;
  var v10$2: bv32;
  var v11$1: bv32;
  var v11$2: bv32;
  var v12$1: bool;
  var v12$2: bool;
  var v13$1: bv32;
  var v13$2: bv32;
  var v14$1: bv32;
  var v14$2: bv32;
  var v15$1: bool;
  var v15$2: bool;
  var v16$1: bv32;
  var v16$2: bv32;
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
  var v35$1: bool;
  var v35$2: bool;
  var v36$1: bv32;
  var v36$2: bv32;
  var v37$1: bv32;
  var v37$2: bv32;
  var v38$1: bv32;
  var v38$2: bv32;
  var v39$1: bv32;
  var v39$2: bv32;
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
    v0$1 := local_id_x$1;
    v0$2 := local_id_x$2;
    v1$1 := local_id_x$1;
    v1$2 := local_id_x$2;
    v2$1 := BV32_UREM(v1$1, 32bv32);
    v2$2 := BV32_UREM(v1$2, 32bv32);
    v3$1 := BV32_UGE(v2$1, 1bv32);
    v3$2 := BV32_UGE(v2$2, 1bv32);
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
    p0$1 := (if v3$1 then v3$1 else p0$1);
    p0$2 := (if v3$2 then v3$2 else p0$2);
    call _PRE_WARP_SYNC_$$A_READ(p0$1, p0$2);
    call _LOG_READ_$$A(p0$1, BV32_SUB(v1$1, 1bv32), $$A[1bv1][BV32_SUB(v1$1, 1bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_32"} {:captureState "check_state_32"} {:sourceloc} {:sourceloc_num 2} true;
    call _CHECK_READ_$$A(p0$2, BV32_SUB(v1$2, 1bv32), $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v1$2, 1bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p0$1, p0$2);
    v4$1 := (if p0$1 then $$A[1bv1][BV32_SUB(v1$1, 1bv32)] else v4$1);
    v4$2 := (if p0$2 then $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v1$2, 1bv32)] else v4$2);
    call _PRE_WARP_SYNC_$$A_READ(p0$1, p0$2);
    call _LOG_READ_$$A(p0$1, v1$1, $$A[1bv1][v1$1]);
    assume {:do_not_predicate} {:check_id "check_state_33"} {:captureState "check_state_33"} {:sourceloc} {:sourceloc_num 3} true;
    call _CHECK_READ_$$A(p0$2, v1$2, $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p0$1, p0$2);
    v5$1 := (if p0$1 then $$A[1bv1][v1$1] else v5$1);
    v5$2 := (if p0$2 then $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2] else v5$2);
    call _PRE_WARP_SYNC_$$A_WRITE(p0$1, p0$2);
    call _LOG_WRITE_$$A(p0$1, v1$1, BV32_ADD(v4$1, v5$1), $$A[1bv1][v1$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(p0$2, v1$2);
    assume {:do_not_predicate} {:check_id "check_state_34"} {:captureState "check_state_34"} {:sourceloc} {:sourceloc_num 4} true;
    call _CHECK_WRITE_$$A(p0$2, v1$2, BV32_ADD(v4$2, v5$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A"} true;
    call _POST_WARP_SYNC_$$A_WRITE(p0$1, p0$2);
    $$A[1bv1][v1$1] := (if p0$1 then BV32_ADD(v4$1, v5$1) else $$A[1bv1][v1$1]);
    $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2] := (if p0$2 then BV32_ADD(v4$2, v5$2) else $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2]);
    v6$1 := BV32_UGE(v2$1, 2bv32);
    v6$2 := BV32_UGE(v2$2, 2bv32);
    p2$1 := (if v6$1 then v6$1 else p2$1);
    p2$2 := (if v6$2 then v6$2 else p2$2);
    call _PRE_WARP_SYNC_$$A_READ(p2$1, p2$2);
    call _LOG_READ_$$A(p2$1, BV32_SUB(v1$1, 2bv32), $$A[1bv1][BV32_SUB(v1$1, 2bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_29"} {:captureState "check_state_29"} {:sourceloc} {:sourceloc_num 7} true;
    call _CHECK_READ_$$A(p2$2, BV32_SUB(v1$2, 2bv32), $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v1$2, 2bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p2$1, p2$2);
    v7$1 := (if p2$1 then $$A[1bv1][BV32_SUB(v1$1, 2bv32)] else v7$1);
    v7$2 := (if p2$2 then $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v1$2, 2bv32)] else v7$2);
    call _PRE_WARP_SYNC_$$A_READ(p2$1, p2$2);
    call _LOG_READ_$$A(p2$1, v1$1, $$A[1bv1][v1$1]);
    assume {:do_not_predicate} {:check_id "check_state_30"} {:captureState "check_state_30"} {:sourceloc} {:sourceloc_num 8} true;
    call _CHECK_READ_$$A(p2$2, v1$2, $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p2$1, p2$2);
    v8$1 := (if p2$1 then $$A[1bv1][v1$1] else v8$1);
    v8$2 := (if p2$2 then $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2] else v8$2);
    call _PRE_WARP_SYNC_$$A_WRITE(p2$1, p2$2);
    call _LOG_WRITE_$$A(p2$1, v1$1, BV32_ADD(v7$1, v8$1), $$A[1bv1][v1$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(p2$2, v1$2);
    assume {:do_not_predicate} {:check_id "check_state_31"} {:captureState "check_state_31"} {:sourceloc} {:sourceloc_num 9} true;
    call _CHECK_WRITE_$$A(p2$2, v1$2, BV32_ADD(v7$2, v8$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A"} true;
    call _POST_WARP_SYNC_$$A_WRITE(p2$1, p2$2);
    $$A[1bv1][v1$1] := (if p2$1 then BV32_ADD(v7$1, v8$1) else $$A[1bv1][v1$1]);
    $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2] := (if p2$2 then BV32_ADD(v7$2, v8$2) else $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2]);
    v9$1 := BV32_UGE(v2$1, 4bv32);
    v9$2 := BV32_UGE(v2$2, 4bv32);
    p4$1 := (if v9$1 then v9$1 else p4$1);
    p4$2 := (if v9$2 then v9$2 else p4$2);
    call _PRE_WARP_SYNC_$$A_READ(p4$1, p4$2);
    call _LOG_READ_$$A(p4$1, BV32_SUB(v1$1, 4bv32), $$A[1bv1][BV32_SUB(v1$1, 4bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_26"} {:captureState "check_state_26"} {:sourceloc} {:sourceloc_num 12} true;
    call _CHECK_READ_$$A(p4$2, BV32_SUB(v1$2, 4bv32), $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v1$2, 4bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p4$1, p4$2);
    v10$1 := (if p4$1 then $$A[1bv1][BV32_SUB(v1$1, 4bv32)] else v10$1);
    v10$2 := (if p4$2 then $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v1$2, 4bv32)] else v10$2);
    call _PRE_WARP_SYNC_$$A_READ(p4$1, p4$2);
    call _LOG_READ_$$A(p4$1, v1$1, $$A[1bv1][v1$1]);
    assume {:do_not_predicate} {:check_id "check_state_27"} {:captureState "check_state_27"} {:sourceloc} {:sourceloc_num 13} true;
    call _CHECK_READ_$$A(p4$2, v1$2, $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p4$1, p4$2);
    v11$1 := (if p4$1 then $$A[1bv1][v1$1] else v11$1);
    v11$2 := (if p4$2 then $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2] else v11$2);
    call _PRE_WARP_SYNC_$$A_WRITE(p4$1, p4$2);
    call _LOG_WRITE_$$A(p4$1, v1$1, BV32_ADD(v10$1, v11$1), $$A[1bv1][v1$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(p4$2, v1$2);
    assume {:do_not_predicate} {:check_id "check_state_28"} {:captureState "check_state_28"} {:sourceloc} {:sourceloc_num 14} true;
    call _CHECK_WRITE_$$A(p4$2, v1$2, BV32_ADD(v10$2, v11$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A"} true;
    call _POST_WARP_SYNC_$$A_WRITE(p4$1, p4$2);
    $$A[1bv1][v1$1] := (if p4$1 then BV32_ADD(v10$1, v11$1) else $$A[1bv1][v1$1]);
    $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2] := (if p4$2 then BV32_ADD(v10$2, v11$2) else $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2]);
    v12$1 := BV32_UGE(v2$1, 8bv32);
    v12$2 := BV32_UGE(v2$2, 8bv32);
    p6$1 := (if v12$1 then v12$1 else p6$1);
    p6$2 := (if v12$2 then v12$2 else p6$2);
    call _PRE_WARP_SYNC_$$A_READ(p6$1, p6$2);
    call _LOG_READ_$$A(p6$1, BV32_SUB(v1$1, 8bv32), $$A[1bv1][BV32_SUB(v1$1, 8bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_23"} {:captureState "check_state_23"} {:sourceloc} {:sourceloc_num 17} true;
    call _CHECK_READ_$$A(p6$2, BV32_SUB(v1$2, 8bv32), $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v1$2, 8bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p6$1, p6$2);
    v13$1 := (if p6$1 then $$A[1bv1][BV32_SUB(v1$1, 8bv32)] else v13$1);
    v13$2 := (if p6$2 then $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v1$2, 8bv32)] else v13$2);
    call _PRE_WARP_SYNC_$$A_READ(p6$1, p6$2);
    call _LOG_READ_$$A(p6$1, v1$1, $$A[1bv1][v1$1]);
    assume {:do_not_predicate} {:check_id "check_state_24"} {:captureState "check_state_24"} {:sourceloc} {:sourceloc_num 18} true;
    call _CHECK_READ_$$A(p6$2, v1$2, $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p6$1, p6$2);
    v14$1 := (if p6$1 then $$A[1bv1][v1$1] else v14$1);
    v14$2 := (if p6$2 then $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2] else v14$2);
    call _PRE_WARP_SYNC_$$A_WRITE(p6$1, p6$2);
    call _LOG_WRITE_$$A(p6$1, v1$1, BV32_ADD(v13$1, v14$1), $$A[1bv1][v1$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(p6$2, v1$2);
    assume {:do_not_predicate} {:check_id "check_state_25"} {:captureState "check_state_25"} {:sourceloc} {:sourceloc_num 19} true;
    call _CHECK_WRITE_$$A(p6$2, v1$2, BV32_ADD(v13$2, v14$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A"} true;
    call _POST_WARP_SYNC_$$A_WRITE(p6$1, p6$2);
    $$A[1bv1][v1$1] := (if p6$1 then BV32_ADD(v13$1, v14$1) else $$A[1bv1][v1$1]);
    $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2] := (if p6$2 then BV32_ADD(v13$2, v14$2) else $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2]);
    v15$1 := BV32_UGE(v2$1, 16bv32);
    v15$2 := BV32_UGE(v2$2, 16bv32);
    p8$1 := (if v15$1 then v15$1 else p8$1);
    p8$2 := (if v15$2 then v15$2 else p8$2);
    call _PRE_WARP_SYNC_$$A_READ(p8$1, p8$2);
    call _LOG_READ_$$A(p8$1, BV32_SUB(v1$1, 16bv32), $$A[1bv1][BV32_SUB(v1$1, 16bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_20"} {:captureState "check_state_20"} {:sourceloc} {:sourceloc_num 22} true;
    call _CHECK_READ_$$A(p8$2, BV32_SUB(v1$2, 16bv32), $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v1$2, 16bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p8$1, p8$2);
    v16$1 := (if p8$1 then $$A[1bv1][BV32_SUB(v1$1, 16bv32)] else v16$1);
    v16$2 := (if p8$2 then $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v1$2, 16bv32)] else v16$2);
    call _PRE_WARP_SYNC_$$A_READ(p8$1, p8$2);
    call _LOG_READ_$$A(p8$1, v1$1, $$A[1bv1][v1$1]);
    assume {:do_not_predicate} {:check_id "check_state_21"} {:captureState "check_state_21"} {:sourceloc} {:sourceloc_num 23} true;
    call _CHECK_READ_$$A(p8$2, v1$2, $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(p8$1, p8$2);
    v17$1 := (if p8$1 then $$A[1bv1][v1$1] else v17$1);
    v17$2 := (if p8$2 then $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2] else v17$2);
    call _PRE_WARP_SYNC_$$A_WRITE(p8$1, p8$2);
    call _LOG_WRITE_$$A(p8$1, v1$1, BV32_ADD(v16$1, v17$1), $$A[1bv1][v1$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(p8$2, v1$2);
    assume {:do_not_predicate} {:check_id "check_state_22"} {:captureState "check_state_22"} {:sourceloc} {:sourceloc_num 24} true;
    call _CHECK_WRITE_$$A(p8$2, v1$2, BV32_ADD(v16$2, v17$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A"} true;
    call _POST_WARP_SYNC_$$A_WRITE(p8$1, p8$2);
    $$A[1bv1][v1$1] := (if p8$1 then BV32_ADD(v16$1, v17$1) else $$A[1bv1][v1$1]);
    $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2] := (if p8$2 then BV32_ADD(v16$2, v17$2) else $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v1$2]);
    goto __partitioned_block_$entry_1;

  __partitioned_block_$entry_1:
    call $bugle_barrier_duplicated_0(1bv1, 0bv1);
    v18$1 := BV32_UREM(v0$1, 32bv32) == 31bv32;
    v18$2 := BV32_UREM(v0$2, 32bv32) == 31bv32;
    p10$1 := (if v18$1 then v18$1 else p10$1);
    p10$2 := (if v18$2 then v18$2 else p10$2);
    call _PRE_WARP_SYNC_$$A_READ(p10$1, p10$2);
    assume {:do_not_predicate} {:check_id "check_state_18"} {:captureState "check_state_18"} {:sourceloc} {:sourceloc_num 28} true;
    call _POST_WARP_SYNC_$$A_READ(p10$1, p10$2);
    v19$1 := (if p10$1 then $$A[1bv1][v0$1] else v19$1);
    v19$2 := (if p10$2 then $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v0$2] else v19$2);
    call _PRE_WARP_SYNC_$$scan.temp_WRITE(p10$1, p10$2);
    call _LOG_WRITE_$$scan.temp(p10$1, BV32_UDIV(v0$1, 32bv32), v19$1, $$scan.temp[1bv1][BV32_UDIV(v0$1, 32bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$scan.temp(p10$2, BV32_UDIV(v0$2, 32bv32));
    assume {:do_not_predicate} {:check_id "check_state_19"} {:captureState "check_state_19"} {:sourceloc} {:sourceloc_num 29} true;
    call _CHECK_WRITE_$$scan.temp(p10$2, BV32_UDIV(v0$2, 32bv32), v19$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$scan.temp"} true;
    call _POST_WARP_SYNC_$$scan.temp_WRITE(p10$1, p10$2);
    $$scan.temp[1bv1][BV32_UDIV(v0$1, 32bv32)] := (if p10$1 then v19$1 else $$scan.temp[1bv1][BV32_UDIV(v0$1, 32bv32)]);
    $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_UDIV(v0$2, 32bv32)] := (if p10$2 then v19$2 else $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_UDIV(v0$2, 32bv32)]);
    goto __partitioned_block_$entry_2;

  __partitioned_block_$entry_2:
    call $bugle_barrier_duplicated_1(1bv1, 0bv1);
    v20$1 := BV32_UDIV(v0$1, 32bv32) == 0bv32;
    v20$2 := BV32_UDIV(v0$2, 32bv32) == 0bv32;
    p12$1 := (if v20$1 then v20$1 else p12$1);
    p12$2 := (if v20$2 then v20$2 else p12$2);
    v21$1 := (if p12$1 then local_id_x$1 else v21$1);
    v21$2 := (if p12$2 then local_id_x$2 else v21$2);
    v22$1 := (if p12$1 then BV32_UREM(v21$1, 32bv32) else v22$1);
    v22$2 := (if p12$2 then BV32_UREM(v21$2, 32bv32) else v22$2);
    v23$1 := (if p12$1 then BV32_UGE(v22$1, 1bv32) else v23$1);
    v23$2 := (if p12$2 then BV32_UGE(v22$2, 1bv32) else v23$2);
    p13$1 := (if p12$1 && v23$1 then v23$1 else p13$1);
    p13$2 := (if p12$2 && v23$2 then v23$2 else p13$2);
    call _PRE_WARP_SYNC_$$scan.temp_READ(p13$1, p13$2);
    call _LOG_READ_$$scan.temp(p13$1, BV32_SUB(v21$1, 1bv32), $$scan.temp[1bv1][BV32_SUB(v21$1, 1bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_15"} {:captureState "check_state_15"} {:sourceloc} {:sourceloc_num 34} true;
    call _CHECK_READ_$$scan.temp(p13$2, BV32_SUB(v21$2, 1bv32), $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v21$2, 1bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$scan.temp"} true;
    call _POST_WARP_SYNC_$$scan.temp_READ(p13$1, p13$2);
    v24$1 := (if p13$1 then $$scan.temp[1bv1][BV32_SUB(v21$1, 1bv32)] else v24$1);
    v24$2 := (if p13$2 then $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v21$2, 1bv32)] else v24$2);
    call _PRE_WARP_SYNC_$$scan.temp_READ(p13$1, p13$2);
    call _LOG_READ_$$scan.temp(p13$1, v21$1, $$scan.temp[1bv1][v21$1]);
    assume {:do_not_predicate} {:check_id "check_state_16"} {:captureState "check_state_16"} {:sourceloc} {:sourceloc_num 35} true;
    call _CHECK_READ_$$scan.temp(p13$2, v21$2, $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$scan.temp"} true;
    call _POST_WARP_SYNC_$$scan.temp_READ(p13$1, p13$2);
    v25$1 := (if p13$1 then $$scan.temp[1bv1][v21$1] else v25$1);
    v25$2 := (if p13$2 then $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2] else v25$2);
    call _PRE_WARP_SYNC_$$scan.temp_WRITE(p13$1, p13$2);
    call _LOG_WRITE_$$scan.temp(p13$1, v21$1, BV32_ADD(v24$1, v25$1), $$scan.temp[1bv1][v21$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$scan.temp(p13$2, v21$2);
    assume {:do_not_predicate} {:check_id "check_state_17"} {:captureState "check_state_17"} {:sourceloc} {:sourceloc_num 36} true;
    call _CHECK_WRITE_$$scan.temp(p13$2, v21$2, BV32_ADD(v24$2, v25$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$scan.temp"} true;
    call _POST_WARP_SYNC_$$scan.temp_WRITE(p13$1, p13$2);
    $$scan.temp[1bv1][v21$1] := (if p13$1 then BV32_ADD(v24$1, v25$1) else $$scan.temp[1bv1][v21$1]);
    $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2] := (if p13$2 then BV32_ADD(v24$2, v25$2) else $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2]);
    v26$1 := (if p12$1 then BV32_UGE(v22$1, 2bv32) else v26$1);
    v26$2 := (if p12$2 then BV32_UGE(v22$2, 2bv32) else v26$2);
    p15$1 := (if p12$1 && v26$1 then v26$1 else p15$1);
    p15$2 := (if p12$2 && v26$2 then v26$2 else p15$2);
    call _PRE_WARP_SYNC_$$scan.temp_READ(p15$1, p15$2);
    call _LOG_READ_$$scan.temp(p15$1, BV32_SUB(v21$1, 2bv32), $$scan.temp[1bv1][BV32_SUB(v21$1, 2bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_12"} {:captureState "check_state_12"} {:sourceloc} {:sourceloc_num 39} true;
    call _CHECK_READ_$$scan.temp(p15$2, BV32_SUB(v21$2, 2bv32), $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v21$2, 2bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$scan.temp"} true;
    call _POST_WARP_SYNC_$$scan.temp_READ(p15$1, p15$2);
    v27$1 := (if p15$1 then $$scan.temp[1bv1][BV32_SUB(v21$1, 2bv32)] else v27$1);
    v27$2 := (if p15$2 then $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v21$2, 2bv32)] else v27$2);
    call _PRE_WARP_SYNC_$$scan.temp_READ(p15$1, p15$2);
    call _LOG_READ_$$scan.temp(p15$1, v21$1, $$scan.temp[1bv1][v21$1]);
    assume {:do_not_predicate} {:check_id "check_state_13"} {:captureState "check_state_13"} {:sourceloc} {:sourceloc_num 40} true;
    call _CHECK_READ_$$scan.temp(p15$2, v21$2, $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$scan.temp"} true;
    call _POST_WARP_SYNC_$$scan.temp_READ(p15$1, p15$2);
    v28$1 := (if p15$1 then $$scan.temp[1bv1][v21$1] else v28$1);
    v28$2 := (if p15$2 then $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2] else v28$2);
    call _PRE_WARP_SYNC_$$scan.temp_WRITE(p15$1, p15$2);
    call _LOG_WRITE_$$scan.temp(p15$1, v21$1, BV32_ADD(v27$1, v28$1), $$scan.temp[1bv1][v21$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$scan.temp(p15$2, v21$2);
    assume {:do_not_predicate} {:check_id "check_state_14"} {:captureState "check_state_14"} {:sourceloc} {:sourceloc_num 41} true;
    call _CHECK_WRITE_$$scan.temp(p15$2, v21$2, BV32_ADD(v27$2, v28$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$scan.temp"} true;
    call _POST_WARP_SYNC_$$scan.temp_WRITE(p15$1, p15$2);
    $$scan.temp[1bv1][v21$1] := (if p15$1 then BV32_ADD(v27$1, v28$1) else $$scan.temp[1bv1][v21$1]);
    $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2] := (if p15$2 then BV32_ADD(v27$2, v28$2) else $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2]);
    v29$1 := (if p12$1 then BV32_UGE(v22$1, 4bv32) else v29$1);
    v29$2 := (if p12$2 then BV32_UGE(v22$2, 4bv32) else v29$2);
    p17$1 := (if p12$1 && v29$1 then v29$1 else p17$1);
    p17$2 := (if p12$2 && v29$2 then v29$2 else p17$2);
    call _PRE_WARP_SYNC_$$scan.temp_READ(p17$1, p17$2);
    call _LOG_READ_$$scan.temp(p17$1, BV32_SUB(v21$1, 4bv32), $$scan.temp[1bv1][BV32_SUB(v21$1, 4bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_9"} {:captureState "check_state_9"} {:sourceloc} {:sourceloc_num 44} true;
    call _CHECK_READ_$$scan.temp(p17$2, BV32_SUB(v21$2, 4bv32), $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v21$2, 4bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$scan.temp"} true;
    call _POST_WARP_SYNC_$$scan.temp_READ(p17$1, p17$2);
    v30$1 := (if p17$1 then $$scan.temp[1bv1][BV32_SUB(v21$1, 4bv32)] else v30$1);
    v30$2 := (if p17$2 then $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v21$2, 4bv32)] else v30$2);
    call _PRE_WARP_SYNC_$$scan.temp_READ(p17$1, p17$2);
    call _LOG_READ_$$scan.temp(p17$1, v21$1, $$scan.temp[1bv1][v21$1]);
    assume {:do_not_predicate} {:check_id "check_state_10"} {:captureState "check_state_10"} {:sourceloc} {:sourceloc_num 45} true;
    call _CHECK_READ_$$scan.temp(p17$2, v21$2, $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$scan.temp"} true;
    call _POST_WARP_SYNC_$$scan.temp_READ(p17$1, p17$2);
    v31$1 := (if p17$1 then $$scan.temp[1bv1][v21$1] else v31$1);
    v31$2 := (if p17$2 then $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2] else v31$2);
    call _PRE_WARP_SYNC_$$scan.temp_WRITE(p17$1, p17$2);
    call _LOG_WRITE_$$scan.temp(p17$1, v21$1, BV32_ADD(v30$1, v31$1), $$scan.temp[1bv1][v21$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$scan.temp(p17$2, v21$2);
    assume {:do_not_predicate} {:check_id "check_state_11"} {:captureState "check_state_11"} {:sourceloc} {:sourceloc_num 46} true;
    call _CHECK_WRITE_$$scan.temp(p17$2, v21$2, BV32_ADD(v30$2, v31$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$scan.temp"} true;
    call _POST_WARP_SYNC_$$scan.temp_WRITE(p17$1, p17$2);
    $$scan.temp[1bv1][v21$1] := (if p17$1 then BV32_ADD(v30$1, v31$1) else $$scan.temp[1bv1][v21$1]);
    $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2] := (if p17$2 then BV32_ADD(v30$2, v31$2) else $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2]);
    v32$1 := (if p12$1 then BV32_UGE(v22$1, 8bv32) else v32$1);
    v32$2 := (if p12$2 then BV32_UGE(v22$2, 8bv32) else v32$2);
    p19$1 := (if p12$1 && v32$1 then v32$1 else p19$1);
    p19$2 := (if p12$2 && v32$2 then v32$2 else p19$2);
    call _PRE_WARP_SYNC_$$scan.temp_READ(p19$1, p19$2);
    call _LOG_READ_$$scan.temp(p19$1, BV32_SUB(v21$1, 8bv32), $$scan.temp[1bv1][BV32_SUB(v21$1, 8bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_6"} {:captureState "check_state_6"} {:sourceloc} {:sourceloc_num 49} true;
    call _CHECK_READ_$$scan.temp(p19$2, BV32_SUB(v21$2, 8bv32), $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v21$2, 8bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$scan.temp"} true;
    call _POST_WARP_SYNC_$$scan.temp_READ(p19$1, p19$2);
    v33$1 := (if p19$1 then $$scan.temp[1bv1][BV32_SUB(v21$1, 8bv32)] else v33$1);
    v33$2 := (if p19$2 then $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v21$2, 8bv32)] else v33$2);
    call _PRE_WARP_SYNC_$$scan.temp_READ(p19$1, p19$2);
    call _LOG_READ_$$scan.temp(p19$1, v21$1, $$scan.temp[1bv1][v21$1]);
    assume {:do_not_predicate} {:check_id "check_state_7"} {:captureState "check_state_7"} {:sourceloc} {:sourceloc_num 50} true;
    call _CHECK_READ_$$scan.temp(p19$2, v21$2, $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$scan.temp"} true;
    call _POST_WARP_SYNC_$$scan.temp_READ(p19$1, p19$2);
    v34$1 := (if p19$1 then $$scan.temp[1bv1][v21$1] else v34$1);
    v34$2 := (if p19$2 then $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2] else v34$2);
    call _PRE_WARP_SYNC_$$scan.temp_WRITE(p19$1, p19$2);
    call _LOG_WRITE_$$scan.temp(p19$1, v21$1, BV32_ADD(v33$1, v34$1), $$scan.temp[1bv1][v21$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$scan.temp(p19$2, v21$2);
    assume {:do_not_predicate} {:check_id "check_state_8"} {:captureState "check_state_8"} {:sourceloc} {:sourceloc_num 51} true;
    call _CHECK_WRITE_$$scan.temp(p19$2, v21$2, BV32_ADD(v33$2, v34$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$scan.temp"} true;
    call _POST_WARP_SYNC_$$scan.temp_WRITE(p19$1, p19$2);
    $$scan.temp[1bv1][v21$1] := (if p19$1 then BV32_ADD(v33$1, v34$1) else $$scan.temp[1bv1][v21$1]);
    $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2] := (if p19$2 then BV32_ADD(v33$2, v34$2) else $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2]);
    v35$1 := (if p12$1 then BV32_UGE(v22$1, 16bv32) else v35$1);
    v35$2 := (if p12$2 then BV32_UGE(v22$2, 16bv32) else v35$2);
    p21$1 := (if p12$1 && v35$1 then v35$1 else p21$1);
    p21$2 := (if p12$2 && v35$2 then v35$2 else p21$2);
    call _PRE_WARP_SYNC_$$scan.temp_READ(p21$1, p21$2);
    call _LOG_READ_$$scan.temp(p21$1, BV32_SUB(v21$1, 16bv32), $$scan.temp[1bv1][BV32_SUB(v21$1, 16bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 54} true;
    call _CHECK_READ_$$scan.temp(p21$2, BV32_SUB(v21$2, 16bv32), $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v21$2, 16bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$scan.temp"} true;
    call _POST_WARP_SYNC_$$scan.temp_READ(p21$1, p21$2);
    v36$1 := (if p21$1 then $$scan.temp[1bv1][BV32_SUB(v21$1, 16bv32)] else v36$1);
    v36$2 := (if p21$2 then $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_SUB(v21$2, 16bv32)] else v36$2);
    call _PRE_WARP_SYNC_$$scan.temp_READ(p21$1, p21$2);
    call _LOG_READ_$$scan.temp(p21$1, v21$1, $$scan.temp[1bv1][v21$1]);
    assume {:do_not_predicate} {:check_id "check_state_4"} {:captureState "check_state_4"} {:sourceloc} {:sourceloc_num 55} true;
    call _CHECK_READ_$$scan.temp(p21$2, v21$2, $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$scan.temp"} true;
    call _POST_WARP_SYNC_$$scan.temp_READ(p21$1, p21$2);
    v37$1 := (if p21$1 then $$scan.temp[1bv1][v21$1] else v37$1);
    v37$2 := (if p21$2 then $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2] else v37$2);
    call _PRE_WARP_SYNC_$$scan.temp_WRITE(p21$1, p21$2);
    call _LOG_WRITE_$$scan.temp(p21$1, v21$1, BV32_ADD(v36$1, v37$1), $$scan.temp[1bv1][v21$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$scan.temp(p21$2, v21$2);
    assume {:do_not_predicate} {:check_id "check_state_5"} {:captureState "check_state_5"} {:sourceloc} {:sourceloc_num 56} true;
    call _CHECK_WRITE_$$scan.temp(p21$2, v21$2, BV32_ADD(v36$2, v37$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$scan.temp"} true;
    call _POST_WARP_SYNC_$$scan.temp_WRITE(p21$1, p21$2);
    $$scan.temp[1bv1][v21$1] := (if p21$1 then BV32_ADD(v36$1, v37$1) else $$scan.temp[1bv1][v21$1]);
    $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2] := (if p21$2 then BV32_ADD(v36$2, v37$2) else $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v21$2]);
    goto __partitioned_block_$entry_3;

  __partitioned_block_$entry_3:
    call $bugle_barrier_duplicated_2(1bv1, 0bv1);
    call _PRE_WARP_SYNC_$$scan.temp_READ(true, true);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 60} true;
    call _POST_WARP_SYNC_$$scan.temp_READ(true, true);
    v38$1 := $$scan.temp[1bv1][BV32_UDIV(v0$1, 32bv32)];
    v38$2 := $$scan.temp[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_UDIV(v0$2, 32bv32)];
    call _PRE_WARP_SYNC_$$A_READ(true, true);
    call _LOG_READ_$$A(true, v0$1, $$A[1bv1][v0$1]);
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 61} true;
    call _CHECK_READ_$$A(true, v0$2, $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v0$2]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$A"} true;
    call _POST_WARP_SYNC_$$A_READ(true, true);
    v39$1 := $$A[1bv1][v0$1];
    v39$2 := $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v0$2];
    call _PRE_WARP_SYNC_$$A_WRITE(true, true);
    call _LOG_WRITE_$$A(true, v0$1, BV32_ADD(v39$1, v38$1), $$A[1bv1][v0$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(true, v0$2);
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 62} true;
    call _CHECK_WRITE_$$A(true, v0$2, BV32_ADD(v39$2, v38$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$A"} true;
    call _POST_WARP_SYNC_$$A_WRITE(true, true);
    $$A[1bv1][v0$1] := BV32_ADD(v39$1, v38$1);
    $$A[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v0$2] := BV32_ADD(v39$2, v38$2);
    return;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 1024bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 1bv32 then 1bv1 else 0bv1) != 0bv1;

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

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_0($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 0bv1;
  modifies $$A, $$scan.temp, _TRACKING;

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_1($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 0bv1;
  modifies $$A, $$scan.temp, _TRACKING;

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_2($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 0bv1;
  modifies $$A, $$scan.temp, _TRACKING;

procedure {:inline 1} _PRE_WARP_SYNC_$$scan.temp_READ(_P$1: bool, _P$2: bool);

procedure {:inline 1} _POST_WARP_SYNC_$$scan.temp_READ(_P$1: bool, _P$2: bool);

procedure {:inline 1} _PRE_WARP_SYNC_$$A_READ(_P$1: bool, _P$2: bool);

procedure {:inline 1} _POST_WARP_SYNC_$$A_READ(_P$1: bool, _P$2: bool);

procedure {:inline 1} _PRE_WARP_SYNC_$$A_WRITE(_P$1: bool, _P$2: bool);

procedure {:inline 1} _POST_WARP_SYNC_$$A_WRITE(_P$1: bool, _P$2: bool);

procedure {:inline 1} _PRE_WARP_SYNC_$$scan.temp_WRITE(_P$1: bool, _P$2: bool);

procedure {:inline 1} _POST_WARP_SYNC_$$scan.temp_WRITE(_P$1: bool, _P$2: bool);

const _WATCHED_VALUE_$$A: bv32;

procedure {:inline 1} _LOG_READ_$$A(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$A;

implementation {:inline 1} _LOG_READ_$$A(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$A := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A == _value then true else _READ_HAS_OCCURRED_$$A);
    return;
}

procedure _CHECK_READ_$$A(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$A && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$A: bool;

procedure {:inline 1} _LOG_WRITE_$$A(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$A, _WRITE_READ_BENIGN_FLAG_$$A;

implementation {:inline 1} _LOG_WRITE_$$A(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$A := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A == _value then true else _WRITE_HAS_OCCURRED_$$A);
    _WRITE_READ_BENIGN_FLAG_$$A := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$A);
    return;
}

procedure _CHECK_WRITE_$$A(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$A != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$A(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$A;

implementation {:inline 1} _LOG_ATOMIC_$$A(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$A := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$A);
    return;
}

procedure _CHECK_ATOMIC_$$A(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$A;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$A(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$A := (if _P && _WRITE_HAS_OCCURRED_$$A && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$A);
    return;
}

const _WATCHED_VALUE_$$scan.temp: bv32;

procedure {:inline 1} _LOG_READ_$$scan.temp(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$scan.temp;

implementation {:inline 1} _LOG_READ_$$scan.temp(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$scan.temp := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$scan.temp == _value then true else _READ_HAS_OCCURRED_$$scan.temp);
    return;
}

procedure _CHECK_READ_$$scan.temp(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$scan.temp && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$scan.temp && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$scan.temp && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$scan.temp: bool;

procedure {:inline 1} _LOG_WRITE_$$scan.temp(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$scan.temp, _WRITE_READ_BENIGN_FLAG_$$scan.temp;

implementation {:inline 1} _LOG_WRITE_$$scan.temp(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$scan.temp := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$scan.temp == _value then true else _WRITE_HAS_OCCURRED_$$scan.temp);
    _WRITE_READ_BENIGN_FLAG_$$scan.temp := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$scan.temp == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$scan.temp);
    return;
}

procedure _CHECK_WRITE_$$scan.temp(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$scan.temp && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$scan.temp != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$scan.temp && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$scan.temp != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$scan.temp && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$scan.temp(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$scan.temp;

implementation {:inline 1} _LOG_ATOMIC_$$scan.temp(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$scan.temp := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$scan.temp);
    return;
}

procedure _CHECK_ATOMIC_$$scan.temp(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$scan.temp && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$scan.temp && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$scan.temp(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$scan.temp;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$scan.temp(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$scan.temp := (if _P && _WRITE_HAS_OCCURRED_$$scan.temp && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$scan.temp);
    return;
}

var _TRACKING: bool;

implementation {:inline 1} $bugle_barrier_duplicated_0($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$A;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$A;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$A;
    goto anon1;

  anon1:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$scan.temp;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$scan.temp;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$scan.temp;
    goto anon2;

  anon2:
    goto anon7_Then, anon7_Else;

  anon7_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon5;

  anon5:
    havoc _TRACKING;
    return;

  anon7_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$A;
    goto anon4;

  anon4:
    havoc $$scan.temp;
    goto anon5;

  anon6_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

implementation {:inline 1} $bugle_barrier_duplicated_1($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$A;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$A;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$A;
    goto anon1;

  anon1:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$scan.temp;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$scan.temp;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$scan.temp;
    goto anon2;

  anon2:
    goto anon7_Then, anon7_Else;

  anon7_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon5;

  anon5:
    havoc _TRACKING;
    return;

  anon7_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$A;
    goto anon4;

  anon4:
    havoc $$scan.temp;
    goto anon5;

  anon6_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

implementation {:inline 1} $bugle_barrier_duplicated_2($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon6_Then, anon6_Else;

  anon6_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$A;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$A;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$A;
    goto anon1;

  anon1:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$scan.temp;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$scan.temp;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$scan.temp;
    goto anon2;

  anon2:
    goto anon7_Then, anon7_Else;

  anon7_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon5;

  anon5:
    havoc _TRACKING;
    return;

  anon7_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$A;
    goto anon4;

  anon4:
    havoc $$scan.temp;
    goto anon5;

  anon6_Then:
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

implementation {:inline 1} _PRE_WARP_SYNC_$$scan.temp_READ(_P$1: bool, _P$2: bool)
{

  entry:
    goto anon0_Then, anon0_Else;

  anon0_Then:
    assume {:partition} _P$1 == _P$2 && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && BV32_DIV(BV32_ADD(local_id_x$1, BV32_ADD(BV32_MUL(local_id_y$1, group_size_x), BV32_MUL(local_id_z$1, BV32_MUL(group_size_x, group_size_y)))), 32bv32) == BV32_DIV(BV32_ADD(local_id_x$2, BV32_ADD(BV32_MUL(local_id_y$2, group_size_x), BV32_MUL(local_id_z$2, BV32_MUL(group_size_x, group_size_y)))), 32bv32);
    goto reset_warps;

  reset_warps:
    assume !_WRITE_HAS_OCCURRED_$$scan.temp;
    assume !_ATOMIC_HAS_OCCURRED_$$scan.temp;
    return;

  anon0_Else:
    assume {:partition} !(_P$1 == _P$2 && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && BV32_DIV(BV32_ADD(local_id_x$1, BV32_ADD(BV32_MUL(local_id_y$1, group_size_x), BV32_MUL(local_id_z$1, BV32_MUL(group_size_x, group_size_y)))), 32bv32) == BV32_DIV(BV32_ADD(local_id_x$2, BV32_ADD(BV32_MUL(local_id_y$2, group_size_x), BV32_MUL(local_id_z$2, BV32_MUL(group_size_x, group_size_y)))), 32bv32));
    return;
}

implementation {:inline 1} _POST_WARP_SYNC_$$scan.temp_READ(_P$1: bool, _P$2: bool)
{

  entry:
    goto anon0_Then, anon0_Else;

  anon0_Then:
    assume {:partition} _P$1 == _P$2 && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && BV32_DIV(BV32_ADD(local_id_x$1, BV32_ADD(BV32_MUL(local_id_y$1, group_size_x), BV32_MUL(local_id_z$1, BV32_MUL(group_size_x, group_size_y)))), 32bv32) == BV32_DIV(BV32_ADD(local_id_x$2, BV32_ADD(BV32_MUL(local_id_y$2, group_size_x), BV32_MUL(local_id_z$2, BV32_MUL(group_size_x, group_size_y)))), 32bv32);
    goto reset_warps;

  reset_warps:
    assume !_READ_HAS_OCCURRED_$$scan.temp;
    return;

  anon0_Else:
    assume {:partition} !(_P$1 == _P$2 && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && BV32_DIV(BV32_ADD(local_id_x$1, BV32_ADD(BV32_MUL(local_id_y$1, group_size_x), BV32_MUL(local_id_z$1, BV32_MUL(group_size_x, group_size_y)))), 32bv32) == BV32_DIV(BV32_ADD(local_id_x$2, BV32_ADD(BV32_MUL(local_id_y$2, group_size_x), BV32_MUL(local_id_z$2, BV32_MUL(group_size_x, group_size_y)))), 32bv32));
    return;
}

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

implementation {:inline 1} _PRE_WARP_SYNC_$$scan.temp_WRITE(_P$1: bool, _P$2: bool)
{

  entry:
    goto anon1_Then, anon1_Else;

  anon1_Then:
    assume {:partition} _P$1 == _P$2 && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && BV32_DIV(BV32_ADD(local_id_x$1, BV32_ADD(BV32_MUL(local_id_y$1, group_size_x), BV32_MUL(local_id_z$1, BV32_MUL(group_size_x, group_size_y)))), 32bv32) == BV32_DIV(BV32_ADD(local_id_x$2, BV32_ADD(BV32_MUL(local_id_y$2, group_size_x), BV32_MUL(local_id_z$2, BV32_MUL(group_size_x, group_size_y)))), 32bv32);
    goto reset_warps;

  reset_warps:
    assume !_READ_HAS_OCCURRED_$$scan.temp;
    assume !_WRITE_HAS_OCCURRED_$$scan.temp;
    assume !_ATOMIC_HAS_OCCURRED_$$scan.temp;
    goto anon0;

  anon0:
    havoc $$scan.temp;
    return;

  anon1_Else:
    assume {:partition} !(_P$1 == _P$2 && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && BV32_DIV(BV32_ADD(local_id_x$1, BV32_ADD(BV32_MUL(local_id_y$1, group_size_x), BV32_MUL(local_id_z$1, BV32_MUL(group_size_x, group_size_y)))), 32bv32) == BV32_DIV(BV32_ADD(local_id_x$2, BV32_ADD(BV32_MUL(local_id_y$2, group_size_x), BV32_MUL(local_id_z$2, BV32_MUL(group_size_x, group_size_y)))), 32bv32));
    return;
}

implementation {:inline 1} _POST_WARP_SYNC_$$scan.temp_WRITE(_P$1: bool, _P$2: bool)
{

  entry:
    goto anon1_Then, anon1_Else;

  anon1_Then:
    assume {:partition} _P$1 == _P$2 && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && BV32_DIV(BV32_ADD(local_id_x$1, BV32_ADD(BV32_MUL(local_id_y$1, group_size_x), BV32_MUL(local_id_z$1, BV32_MUL(group_size_x, group_size_y)))), 32bv32) == BV32_DIV(BV32_ADD(local_id_x$2, BV32_ADD(BV32_MUL(local_id_y$2, group_size_x), BV32_MUL(local_id_z$2, BV32_MUL(group_size_x, group_size_y)))), 32bv32);
    goto reset_warps;

  reset_warps:
    assume !_WRITE_HAS_OCCURRED_$$scan.temp;
    goto anon0;

  anon0:
    havoc $$scan.temp;
    return;

  anon1_Else:
    assume {:partition} !(_P$1 == _P$2 && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && BV32_DIV(BV32_ADD(local_id_x$1, BV32_ADD(BV32_MUL(local_id_y$1, group_size_x), BV32_MUL(local_id_z$1, BV32_MUL(group_size_x, group_size_y)))), 32bv32) == BV32_DIV(BV32_ADD(local_id_x$2, BV32_ADD(BV32_MUL(local_id_y$2, group_size_x), BV32_MUL(local_id_z$2, BV32_MUL(group_size_x, group_size_y)))), 32bv32));
    return;
}

