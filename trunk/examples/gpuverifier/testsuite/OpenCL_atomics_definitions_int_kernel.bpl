//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(y: bv32, x$1: [bv32]bv32, x$2: [bv32]bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);
  requires y == 0bv32;

axiom {:array_info "$$A"} {:group_shared} {:elem_width 32} {:source_name "A"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$A: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$A: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$A: bool;

axiom {:array_info "$$B"} {:group_shared} {:elem_width 32} {:source_name "B"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$B: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$B: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$B: bool;

axiom {:array_info "$$C"} {:global} {:elem_width 32} {:source_name "C"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$C: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$C: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$C: bool;

axiom {:array_info "$$D"} {:global} {:elem_width 32} {:source_name "D"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$D: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$D: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$D: bool;

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

procedure {:source_name "definitions"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$C && !_WRITE_HAS_OCCURRED_$$C && !_ATOMIC_HAS_OCCURRED_$$C;
  requires !_READ_HAS_OCCURRED_$$D && !_WRITE_HAS_OCCURRED_$$D && !_ATOMIC_HAS_OCCURRED_$$D;
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
  modifies _ATOMIC_HAS_OCCURRED_$$A, _ATOMIC_HAS_OCCURRED_$$B, _ATOMIC_HAS_OCCURRED_$$C, _ATOMIC_HAS_OCCURRED_$$D;

implementation {:source_name "definitions"} ULTIMATE.start()
{
  var v0$1: bv32;
  var v0$2: bv32;
  var v1$1: bv32;
  var v1$2: bv32;
  var v2$1: bv32;
  var v2$2: bv32;
  var v3$1: bv32;
  var v3$2: bv32;
  var v4$1: bv32;
  var v4$2: bv32;
  var v5$1: bv32;
  var v5$2: bv32;
  var v6$1: bv32;
  var v6$2: bv32;
  var v16$1: bv32;
  var v16$2: bv32;
  var v8$1: bv32;
  var v8$2: bv32;
  var v7$1: bv32;
  var v7$2: bv32;
  var v10$1: bv32;
  var v10$2: bv32;
  var v9$1: bv32;
  var v9$2: bv32;
  var v11$1: bv32;
  var v11$2: bv32;
  var v12$1: bv32;
  var v12$2: bv32;
  var v14$1: bv32;
  var v14$2: bv32;
  var v13$1: bv32;
  var v13$2: bv32;
  var v15$1: bv32;
  var v15$2: bv32;
  var v32$1: bv32;
  var v32$2: bv32;
  var v17$1: bv32;
  var v17$2: bv32;
  var v20$1: bv32;
  var v20$2: bv32;
  var v18$1: bv32;
  var v18$2: bv32;
  var v19$1: bv32;
  var v19$2: bv32;
  var v21$1: bv32;
  var v21$2: bv32;
  var v22$1: bv32;
  var v22$2: bv32;
  var v23$1: bv32;
  var v23$2: bv32;
  var v24$1: bv32;
  var v24$2: bv32;
  var v25$1: bv32;
  var v25$2: bv32;
  var v26$1: bv32;
  var v26$2: bv32;
  var v27$1: bv32;
  var v27$2: bv32;
  var v28$1: bv32;
  var v28$2: bv32;
  var v29$1: bv32;
  var v29$2: bv32;
  var v30$1: bv32;
  var v30$2: bv32;
  var v33$1: bv32;
  var v33$2: bv32;
  var v31$1: bv32;
  var v31$2: bv32;
  var v34$1: bv32;
  var v34$2: bv32;
  var v35$1: bv32;
  var v35$2: bv32;
  var v36$1: bv32;
  var v36$2: bv32;
  var v37$1: bv32;
  var v37$2: bv32;
  var v38$1: bv32;
  var v38$2: bv32;
  var v39$1: bv32;
  var v39$2: bv32;
  var v40$1: bv32;
  var v40$2: bv32;
  var v41$1: bv32;
  var v41$2: bv32;
  var v43$1: bv32;
  var v43$2: bv32;
  var v42$1: bv32;
  var v42$2: bv32;

  $entry:
    call _LOG_ATOMIC_$$A(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 1} true;
    call _CHECK_ATOMIC_$$A(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$A"} true;
    havoc v0$1, v0$2;
    call _LOG_ATOMIC_$$A(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 2} true;
    call _CHECK_ATOMIC_$$A(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$A"} true;
    havoc v1$1, v1$2;
    call _LOG_ATOMIC_$$A(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 3} true;
    call _CHECK_ATOMIC_$$A(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$A"} true;
    havoc v2$1, v2$2;
    call _LOG_ATOMIC_$$A(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 4} true;
    call _CHECK_ATOMIC_$$A(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$A"} true;
    havoc v3$1, v3$2;
    call _LOG_ATOMIC_$$A(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_4"} {:captureState "check_state_4"} {:sourceloc} {:sourceloc_num 5} true;
    call _CHECK_ATOMIC_$$A(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$A"} true;
    havoc v4$1, v4$2;
    call _LOG_ATOMIC_$$A(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_5"} {:captureState "check_state_5"} {:sourceloc} {:sourceloc_num 6} true;
    call _CHECK_ATOMIC_$$A(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$A"} true;
    havoc v5$1, v5$2;
    call _LOG_ATOMIC_$$A(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_6"} {:captureState "check_state_6"} {:sourceloc} {:sourceloc_num 7} true;
    call _CHECK_ATOMIC_$$A(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$A"} true;
    havoc v6$1, v6$2;
    call _LOG_ATOMIC_$$A(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_7"} {:captureState "check_state_7"} {:sourceloc} {:sourceloc_num 8} true;
    call _CHECK_ATOMIC_$$A(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$A"} true;
    havoc v7$1, v7$2;
    call _LOG_ATOMIC_$$A(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_8"} {:captureState "check_state_8"} {:sourceloc} {:sourceloc_num 9} true;
    call _CHECK_ATOMIC_$$A(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$A"} true;
    havoc v8$1, v8$2;
    call _LOG_ATOMIC_$$A(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_9"} {:captureState "check_state_9"} {:sourceloc} {:sourceloc_num 10} true;
    call _CHECK_ATOMIC_$$A(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$A"} true;
    havoc v9$1, v9$2;
    call _LOG_ATOMIC_$$A(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_10"} {:captureState "check_state_10"} {:sourceloc} {:sourceloc_num 11} true;
    call _CHECK_ATOMIC_$$A(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$A"} true;
    havoc v10$1, v10$2;
    call _LOG_ATOMIC_$$B(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_11"} {:captureState "check_state_11"} {:sourceloc} {:sourceloc_num 12} true;
    call _CHECK_ATOMIC_$$B(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$B"} true;
    havoc v11$1, v11$2;
    call _LOG_ATOMIC_$$B(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_12"} {:captureState "check_state_12"} {:sourceloc} {:sourceloc_num 13} true;
    call _CHECK_ATOMIC_$$B(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$B"} true;
    havoc v12$1, v12$2;
    call _LOG_ATOMIC_$$B(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_13"} {:captureState "check_state_13"} {:sourceloc} {:sourceloc_num 14} true;
    call _CHECK_ATOMIC_$$B(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$B"} true;
    havoc v13$1, v13$2;
    call _LOG_ATOMIC_$$B(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_14"} {:captureState "check_state_14"} {:sourceloc} {:sourceloc_num 15} true;
    call _CHECK_ATOMIC_$$B(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$B"} true;
    havoc v14$1, v14$2;
    call _LOG_ATOMIC_$$B(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_15"} {:captureState "check_state_15"} {:sourceloc} {:sourceloc_num 16} true;
    call _CHECK_ATOMIC_$$B(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$B"} true;
    havoc v15$1, v15$2;
    call _LOG_ATOMIC_$$B(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_16"} {:captureState "check_state_16"} {:sourceloc} {:sourceloc_num 17} true;
    call _CHECK_ATOMIC_$$B(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$B"} true;
    havoc v16$1, v16$2;
    call _LOG_ATOMIC_$$B(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_17"} {:captureState "check_state_17"} {:sourceloc} {:sourceloc_num 18} true;
    call _CHECK_ATOMIC_$$B(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$B"} true;
    havoc v17$1, v17$2;
    call _LOG_ATOMIC_$$B(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_18"} {:captureState "check_state_18"} {:sourceloc} {:sourceloc_num 19} true;
    call _CHECK_ATOMIC_$$B(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$B"} true;
    havoc v18$1, v18$2;
    call _LOG_ATOMIC_$$B(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_19"} {:captureState "check_state_19"} {:sourceloc} {:sourceloc_num 20} true;
    call _CHECK_ATOMIC_$$B(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$B"} true;
    havoc v19$1, v19$2;
    call _LOG_ATOMIC_$$B(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_20"} {:captureState "check_state_20"} {:sourceloc} {:sourceloc_num 21} true;
    call _CHECK_ATOMIC_$$B(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$B"} true;
    havoc v20$1, v20$2;
    call _LOG_ATOMIC_$$B(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_21"} {:captureState "check_state_21"} {:sourceloc} {:sourceloc_num 22} true;
    call _CHECK_ATOMIC_$$B(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$B"} true;
    havoc v21$1, v21$2;
    call _LOG_ATOMIC_$$C(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_22"} {:captureState "check_state_22"} {:sourceloc} {:sourceloc_num 23} true;
    call _CHECK_ATOMIC_$$C(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$C"} true;
    havoc v22$1, v22$2;
    call _LOG_ATOMIC_$$C(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_23"} {:captureState "check_state_23"} {:sourceloc} {:sourceloc_num 24} true;
    call _CHECK_ATOMIC_$$C(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$C"} true;
    havoc v23$1, v23$2;
    call _LOG_ATOMIC_$$C(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_24"} {:captureState "check_state_24"} {:sourceloc} {:sourceloc_num 25} true;
    call _CHECK_ATOMIC_$$C(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$C"} true;
    havoc v24$1, v24$2;
    call _LOG_ATOMIC_$$C(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_25"} {:captureState "check_state_25"} {:sourceloc} {:sourceloc_num 26} true;
    call _CHECK_ATOMIC_$$C(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$C"} true;
    havoc v25$1, v25$2;
    call _LOG_ATOMIC_$$C(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_26"} {:captureState "check_state_26"} {:sourceloc} {:sourceloc_num 27} true;
    call _CHECK_ATOMIC_$$C(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$C"} true;
    havoc v26$1, v26$2;
    call _LOG_ATOMIC_$$C(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_27"} {:captureState "check_state_27"} {:sourceloc} {:sourceloc_num 28} true;
    call _CHECK_ATOMIC_$$C(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$C"} true;
    havoc v27$1, v27$2;
    call _LOG_ATOMIC_$$C(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_28"} {:captureState "check_state_28"} {:sourceloc} {:sourceloc_num 29} true;
    call _CHECK_ATOMIC_$$C(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$C"} true;
    havoc v28$1, v28$2;
    call _LOG_ATOMIC_$$C(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_29"} {:captureState "check_state_29"} {:sourceloc} {:sourceloc_num 30} true;
    call _CHECK_ATOMIC_$$C(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$C"} true;
    havoc v29$1, v29$2;
    call _LOG_ATOMIC_$$C(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_30"} {:captureState "check_state_30"} {:sourceloc} {:sourceloc_num 31} true;
    call _CHECK_ATOMIC_$$C(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$C"} true;
    havoc v30$1, v30$2;
    call _LOG_ATOMIC_$$C(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_31"} {:captureState "check_state_31"} {:sourceloc} {:sourceloc_num 32} true;
    call _CHECK_ATOMIC_$$C(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$C"} true;
    havoc v31$1, v31$2;
    call _LOG_ATOMIC_$$C(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_32"} {:captureState "check_state_32"} {:sourceloc} {:sourceloc_num 33} true;
    call _CHECK_ATOMIC_$$C(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$C"} true;
    havoc v32$1, v32$2;
    call _LOG_ATOMIC_$$D(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_33"} {:captureState "check_state_33"} {:sourceloc} {:sourceloc_num 34} true;
    call _CHECK_ATOMIC_$$D(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$D"} true;
    havoc v33$1, v33$2;
    call _LOG_ATOMIC_$$D(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_34"} {:captureState "check_state_34"} {:sourceloc} {:sourceloc_num 35} true;
    call _CHECK_ATOMIC_$$D(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$D"} true;
    havoc v34$1, v34$2;
    call _LOG_ATOMIC_$$D(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_35"} {:captureState "check_state_35"} {:sourceloc} {:sourceloc_num 36} true;
    call _CHECK_ATOMIC_$$D(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$D"} true;
    havoc v35$1, v35$2;
    call _LOG_ATOMIC_$$D(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_36"} {:captureState "check_state_36"} {:sourceloc} {:sourceloc_num 37} true;
    call _CHECK_ATOMIC_$$D(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$D"} true;
    havoc v36$1, v36$2;
    call _LOG_ATOMIC_$$D(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_37"} {:captureState "check_state_37"} {:sourceloc} {:sourceloc_num 38} true;
    call _CHECK_ATOMIC_$$D(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$D"} true;
    havoc v37$1, v37$2;
    call _LOG_ATOMIC_$$D(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_38"} {:captureState "check_state_38"} {:sourceloc} {:sourceloc_num 39} true;
    call _CHECK_ATOMIC_$$D(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$D"} true;
    havoc v38$1, v38$2;
    call _LOG_ATOMIC_$$D(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_39"} {:captureState "check_state_39"} {:sourceloc} {:sourceloc_num 40} true;
    call _CHECK_ATOMIC_$$D(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$D"} true;
    havoc v39$1, v39$2;
    call _LOG_ATOMIC_$$D(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_40"} {:captureState "check_state_40"} {:sourceloc} {:sourceloc_num 41} true;
    call _CHECK_ATOMIC_$$D(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$D"} true;
    havoc v40$1, v40$2;
    call _LOG_ATOMIC_$$D(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_41"} {:captureState "check_state_41"} {:sourceloc} {:sourceloc_num 42} true;
    call _CHECK_ATOMIC_$$D(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$D"} true;
    havoc v41$1, v41$2;
    call _LOG_ATOMIC_$$D(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_42"} {:captureState "check_state_42"} {:sourceloc} {:sourceloc_num 43} true;
    call _CHECK_ATOMIC_$$D(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$D"} true;
    havoc v42$1, v42$2;
    call _LOG_ATOMIC_$$D(true, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_43"} {:captureState "check_state_43"} {:sourceloc} {:sourceloc_num 44} true;
    call _CHECK_ATOMIC_$$D(true, 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_ATOMIC_$$D"} true;
    havoc v43$1, v43$2;
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

const _WATCHED_VALUE_$$C: bv32;

procedure {:inline 1} _LOG_READ_$$C(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$C;

implementation {:inline 1} _LOG_READ_$$C(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$C := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$C == _value then true else _READ_HAS_OCCURRED_$$C);
    return;
}

procedure _CHECK_READ_$$C(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$C && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$C);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$C && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$C: bool;

procedure {:inline 1} _LOG_WRITE_$$C(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$C, _WRITE_READ_BENIGN_FLAG_$$C;

implementation {:inline 1} _LOG_WRITE_$$C(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$C := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$C == _value then true else _WRITE_HAS_OCCURRED_$$C);
    _WRITE_READ_BENIGN_FLAG_$$C := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$C == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$C);
    return;
}

procedure _CHECK_WRITE_$$C(_P: bool, _offset: bv32, _value: bv32);
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

const _WATCHED_VALUE_$$D: bv32;

procedure {:inline 1} _LOG_READ_$$D(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$D;

implementation {:inline 1} _LOG_READ_$$D(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$D := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$D == _value then true else _READ_HAS_OCCURRED_$$D);
    return;
}

procedure _CHECK_READ_$$D(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$D && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$D);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$D && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$D: bool;

procedure {:inline 1} _LOG_WRITE_$$D(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$D, _WRITE_READ_BENIGN_FLAG_$$D;

implementation {:inline 1} _LOG_WRITE_$$D(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$D := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$D == _value then true else _WRITE_HAS_OCCURRED_$$D);
    _WRITE_READ_BENIGN_FLAG_$$D := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$D == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$D);
    return;
}

procedure _CHECK_WRITE_$$D(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$D && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$D != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$D && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$D != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$D && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$D(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$D;

implementation {:inline 1} _LOG_ATOMIC_$$D(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$D := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$D);
    return;
}

procedure _CHECK_ATOMIC_$$D(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$D && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$D && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$D(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$D;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$D(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$D := (if _P && _WRITE_HAS_OCCURRED_$$D && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$D);
    return;
}

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

const _WATCHED_VALUE_$$B: bv32;

procedure {:inline 1} _LOG_READ_$$B(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$B;

implementation {:inline 1} _LOG_READ_$$B(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$B := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$B == _value then true else _READ_HAS_OCCURRED_$$B);
    return;
}

procedure _CHECK_READ_$$B(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$B && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$B && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$B && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$B: bool;

procedure {:inline 1} _LOG_WRITE_$$B(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$B, _WRITE_READ_BENIGN_FLAG_$$B;

implementation {:inline 1} _LOG_WRITE_$$B(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$B := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$B == _value then true else _WRITE_HAS_OCCURRED_$$B);
    _WRITE_READ_BENIGN_FLAG_$$B := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$B == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$B);
    return;
}

procedure _CHECK_WRITE_$$B(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$B && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$B != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$B && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$B != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$B && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$B(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$B;

implementation {:inline 1} _LOG_ATOMIC_$$B(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$B := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$B);
    return;
}

procedure _CHECK_ATOMIC_$$B(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$B && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$B && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

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
