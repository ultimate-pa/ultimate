//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP8(x: [bv32]bv8, y: bv32) returns (z$1: bv8, A$1: [bv32]bv8, z$2: bv8, A$2: [bv32]bv8);

axiom {:array_info "$$acc"} {:elem_width 8} {:source_name "acc"} {:source_elem_width 128} {:source_dimensions "1"} true;

axiom {:array_info "$$res1"} {:elem_width 8} {:source_name "res1"} {:source_elem_width 32} {:source_dimensions "1"} true;

axiom {:array_info "$$res2"} {:elem_width 8} {:source_name "res2"} {:source_elem_width 32} {:source_dimensions "1"} true;

axiom {:array_info "$$res3"} {:elem_width 8} {:source_name "res3"} {:source_elem_width 32} {:source_dimensions "1"} true;

axiom {:array_info "$$res4"} {:elem_width 8} {:source_name "res4"} {:source_elem_width 32} {:source_dimensions "1"} true;

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

function FADD32(bv32, bv32) : bv32;

function FMUL32(bv32, bv32) : bv32;

function {:builtin "sign_extend 24"} BV8_SEXT32(bv8) : bv32;

procedure {:source_name "foo"} ULTIMATE.start();
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

implementation {:source_name "foo"} ULTIMATE.start()
{
  var $0$1: bv1;
  var $0$2: bv1;
  var $1$1: bv1;
  var $1$2: bv1;
  var $2$1: bv1;
  var $2$2: bv1;
  var $3$1: bv1;
  var $3$2: bv1;
  var v7$1: bv8;
  var v7$2: bv8;
  var v8$1: bv8;
  var v8$2: bv8;
  var v0$1: bv8;
  var v0$2: bv8;
  var v1$1: bv8;
  var v1$2: bv8;
  var v2$1: bv8;
  var v2$2: bv8;
  var v3$1: bv8;
  var v3$2: bv8;
  var v4$1: bv8;
  var v4$2: bv8;
  var v5$1: bv8;
  var v5$2: bv8;
  var v6$1: bv8;
  var v6$2: bv8;
  var v9$1: bv8;
  var v9$2: bv8;
  var v10$1: bv8;
  var v10$2: bv8;
  var v11$1: bv8;
  var v11$2: bv8;
  var v12$1: bv8;
  var v12$2: bv8;
  var v13$1: bv8;
  var v13$2: bv8;
  var v14$1: bv8;
  var v14$2: bv8;
  var v15$1: bv8;
  var v15$2: bv8;
  var v16$1: bv32;
  var v16$2: bv32;
  var v17$1: bv32;
  var v17$2: bv32;
  var v18$1: bv32;
  var v18$2: bv32;
  var v19$1: bv32;
  var v19$2: bv32;
  var v21: bv32;
  var v20: bv32;
  var v22: bv32;
  var v23: bv32;
  var v24$1: bv8;
  var v24$2: bv8;
  var v25$1: bv8;
  var v25$2: bv8;
  var v26$1: bool;
  var v26$2: bool;
  var v27$1: bv8;
  var v27$2: bv8;
  var v28$1: bv8;
  var v28$2: bv8;
  var v29$1: bool;
  var v29$2: bool;
  var v30$1: bv8;
  var v30$2: bv8;
  var v31$1: bv8;
  var v31$2: bv8;
  var v32$1: bool;
  var v32$2: bool;
  var v33$1: bv8;
  var v33$2: bv8;
  var v34$1: bv8;
  var v34$2: bv8;
  var v35$1: bv8;
  var v35$2: bv8;
  var v36$1: bv8;
  var v36$2: bv8;
  var v37$1: bool;
  var v37$2: bool;
  var v38$1: bv8;
  var v38$2: bv8;
  var v39$1: bv8;
  var v39$2: bv8;
  var v40$1: bool;
  var v40$2: bool;
  var v41$1: bv8;
  var v41$2: bv8;
  var v42$1: bv8;
  var v42$2: bv8;
  var v43$1: bool;
  var v43$2: bool;
  var v44$1: bv8;
  var v44$2: bv8;
  var v45$1: bv8;
  var v45$2: bv8;
  var v46$1: bv8;
  var v46$2: bv8;
  var v47$1: bv8;
  var v47$2: bv8;
  var v48$1: bool;
  var v48$2: bool;
  var v49$1: bv8;
  var v49$2: bv8;
  var v50$1: bv8;
  var v50$2: bv8;
  var v51$1: bool;
  var v51$2: bool;
  var v52$1: bv8;
  var v52$2: bv8;
  var v53$1: bv8;
  var v53$2: bv8;
  var v54$1: bool;
  var v54$2: bool;
  var v55$1: bv8;
  var v55$2: bv8;
  var v56$1: bv8;
  var v56$2: bv8;
  var v57$1: bv8;
  var v57$2: bv8;
  var v58$1: bv8;
  var v58$2: bv8;
  var v59$1: bool;
  var v59$2: bool;
  var v60$1: bv8;
  var v60$2: bv8;
  var v61$1: bv8;
  var v61$2: bv8;
  var v62$1: bool;
  var v62$2: bool;
  var v63$1: bv8;
  var v63$2: bv8;
  var v64$1: bv8;
  var v64$2: bv8;
  var v65$1: bool;
  var v65$2: bool;
  var v66$1: bv8;
  var v66$2: bv8;
  var v67$1: bv8;
  var v67$2: bv8;
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

  $entry:
    $$acc$0bv32$1 := 0bv8;
    $$acc$0bv32$2 := 0bv8;
    $$acc$1bv32$1 := 0bv8;
    $$acc$1bv32$2 := 0bv8;
    $$acc$2bv32$1 := 128bv8;
    $$acc$2bv32$2 := 128bv8;
    $$acc$3bv32$1 := 63bv8;
    $$acc$3bv32$2 := 63bv8;
    $$acc$4bv32$1 := 0bv8;
    $$acc$4bv32$2 := 0bv8;
    $$acc$5bv32$1 := 0bv8;
    $$acc$5bv32$2 := 0bv8;
    $$acc$6bv32$1 := 128bv8;
    $$acc$6bv32$2 := 128bv8;
    $$acc$7bv32$1 := 63bv8;
    $$acc$7bv32$2 := 63bv8;
    $$acc$8bv32$1 := 0bv8;
    $$acc$8bv32$2 := 0bv8;
    $$acc$9bv32$1 := 0bv8;
    $$acc$9bv32$2 := 0bv8;
    $$acc$10bv32$1 := 128bv8;
    $$acc$10bv32$2 := 128bv8;
    $$acc$11bv32$1 := 63bv8;
    $$acc$11bv32$2 := 63bv8;
    $$acc$12bv32$1 := 0bv8;
    $$acc$12bv32$2 := 0bv8;
    $$acc$13bv32$1 := 0bv8;
    $$acc$13bv32$2 := 0bv8;
    $$acc$14bv32$1 := 128bv8;
    $$acc$14bv32$2 := 128bv8;
    $$acc$15bv32$1 := 63bv8;
    $$acc$15bv32$2 := 63bv8;
    v0$1 := $$acc$0bv32$1;
    v0$2 := $$acc$0bv32$2;
    v1$1 := $$acc$1bv32$1;
    v1$2 := $$acc$1bv32$2;
    v2$1 := $$acc$2bv32$1;
    v2$2 := $$acc$2bv32$2;
    v3$1 := $$acc$3bv32$1;
    v3$2 := $$acc$3bv32$2;
    v4$1 := $$acc$4bv32$1;
    v4$2 := $$acc$4bv32$2;
    v5$1 := $$acc$5bv32$1;
    v5$2 := $$acc$5bv32$2;
    v6$1 := $$acc$6bv32$1;
    v6$2 := $$acc$6bv32$2;
    v7$1 := $$acc$7bv32$1;
    v7$2 := $$acc$7bv32$2;
    v8$1 := $$acc$8bv32$1;
    v8$2 := $$acc$8bv32$2;
    v9$1 := $$acc$9bv32$1;
    v9$2 := $$acc$9bv32$2;
    v10$1 := $$acc$10bv32$1;
    v10$2 := $$acc$10bv32$2;
    v11$1 := $$acc$11bv32$1;
    v11$2 := $$acc$11bv32$2;
    v12$1 := $$acc$12bv32$1;
    v12$2 := $$acc$12bv32$2;
    v13$1 := $$acc$13bv32$1;
    v13$2 := $$acc$13bv32$2;
    v14$1 := $$acc$14bv32$1;
    v14$2 := $$acc$14bv32$2;
    v15$1 := $$acc$15bv32$1;
    v15$2 := $$acc$15bv32$2;
    v16$1 := FADD32(FMUL32(1065353216bv32, 1073741824bv32), v3$1 ++ v2$1 ++ v1$1 ++ v0$1);
    v16$2 := FADD32(FMUL32(1065353216bv32, 1073741824bv32), v3$2 ++ v2$2 ++ v1$2 ++ v0$2);
    v17$1 := FADD32(FMUL32(1073741824bv32, 1073741824bv32), v7$1 ++ v6$1 ++ v5$1 ++ v4$1);
    v17$2 := FADD32(FMUL32(1073741824bv32, 1073741824bv32), v7$2 ++ v6$2 ++ v5$2 ++ v4$2);
    v18$1 := FADD32(FMUL32(1077936128bv32, 1073741824bv32), v11$1 ++ v10$1 ++ v9$1 ++ v8$1);
    v18$2 := FADD32(FMUL32(1077936128bv32, 1073741824bv32), v11$2 ++ v10$2 ++ v9$2 ++ v8$2);
    v19$1 := FADD32(FMUL32(1082130432bv32, 1073741824bv32), v15$1 ++ v14$1 ++ v13$1 ++ v12$1);
    v19$2 := FADD32(FMUL32(1082130432bv32, 1073741824bv32), v15$2 ++ v14$2 ++ v13$2 ++ v12$2);
    $$acc$0bv32$1 := v16$1[8:0];
    $$acc$0bv32$2 := v16$2[8:0];
    $$acc$1bv32$1 := v16$1[16:8];
    $$acc$1bv32$2 := v16$2[16:8];
    $$acc$2bv32$1 := v16$1[24:16];
    $$acc$2bv32$2 := v16$2[24:16];
    $$acc$3bv32$1 := v16$1[32:24];
    $$acc$3bv32$2 := v16$2[32:24];
    $$acc$4bv32$1 := v17$1[8:0];
    $$acc$4bv32$2 := v17$2[8:0];
    $$acc$5bv32$1 := v17$1[16:8];
    $$acc$5bv32$2 := v17$2[16:8];
    $$acc$6bv32$1 := v17$1[24:16];
    $$acc$6bv32$2 := v17$2[24:16];
    $$acc$7bv32$1 := v17$1[32:24];
    $$acc$7bv32$2 := v17$2[32:24];
    $$acc$8bv32$1 := v18$1[8:0];
    $$acc$8bv32$2 := v18$2[8:0];
    $$acc$9bv32$1 := v18$1[16:8];
    $$acc$9bv32$2 := v18$2[16:8];
    $$acc$10bv32$1 := v18$1[24:16];
    $$acc$10bv32$2 := v18$2[24:16];
    $$acc$11bv32$1 := v18$1[32:24];
    $$acc$11bv32$2 := v18$2[32:24];
    $$acc$12bv32$1 := v19$1[8:0];
    $$acc$12bv32$2 := v19$2[8:0];
    $$acc$13bv32$1 := v19$1[16:8];
    $$acc$13bv32$2 := v19$2[16:8];
    $$acc$14bv32$1 := v19$1[24:16];
    $$acc$14bv32$2 := v19$2[24:16];
    $$acc$15bv32$1 := v19$1[32:24];
    $$acc$15bv32$2 := v19$2[32:24];
    v20 := FADD32(FMUL32(1065353216bv32, 1073741824bv32), 1065353216bv32);
    $$res1$0bv32$1 := v20[8:0];
    $$res1$0bv32$2 := v20[8:0];
    $$res1$1bv32$1 := v20[16:8];
    $$res1$1bv32$2 := v20[16:8];
    $$res1$2bv32$1 := v20[24:16];
    $$res1$2bv32$2 := v20[24:16];
    $$res1$3bv32$1 := v20[32:24];
    $$res1$3bv32$2 := v20[32:24];
    v21 := FADD32(FMUL32(1073741824bv32, 1073741824bv32), 1065353216bv32);
    $$res2$0bv32$1 := v21[8:0];
    $$res2$0bv32$2 := v21[8:0];
    $$res2$1bv32$1 := v21[16:8];
    $$res2$1bv32$2 := v21[16:8];
    $$res2$2bv32$1 := v21[24:16];
    $$res2$2bv32$2 := v21[24:16];
    $$res2$3bv32$1 := v21[32:24];
    $$res2$3bv32$2 := v21[32:24];
    v22 := FADD32(FMUL32(1077936128bv32, 1073741824bv32), 1065353216bv32);
    $$res3$0bv32$1 := v22[8:0];
    $$res3$0bv32$2 := v22[8:0];
    $$res3$1bv32$1 := v22[16:8];
    $$res3$1bv32$2 := v22[16:8];
    $$res3$2bv32$1 := v22[24:16];
    $$res3$2bv32$2 := v22[24:16];
    $$res3$3bv32$1 := v22[32:24];
    $$res3$3bv32$2 := v22[32:24];
    v23 := FADD32(FMUL32(1082130432bv32, 1073741824bv32), 1065353216bv32);
    $$res4$0bv32$1 := v23[8:0];
    $$res4$0bv32$2 := v23[8:0];
    $$res4$1bv32$1 := v23[16:8];
    $$res4$1bv32$2 := v23[16:8];
    $$res4$2bv32$1 := v23[24:16];
    $$res4$2bv32$2 := v23[24:16];
    $$res4$3bv32$1 := v23[32:24];
    $$res4$3bv32$2 := v23[32:24];
    v24$1 := $$acc$0bv32$1;
    v24$2 := $$acc$0bv32$2;
    v25$1 := $$res1$0bv32$1;
    v25$2 := $$res1$0bv32$2;
    v26$1 := BV8_SEXT32(v24$1) == BV8_SEXT32(v25$1);
    v26$2 := BV8_SEXT32(v24$2) == BV8_SEXT32(v25$2);
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
    p0$1 := (if v26$1 then v26$1 else p0$1);
    p0$2 := (if v26$2 then v26$2 else p0$2);
    p5$1 := (if !v26$1 then !v26$1 else p5$1);
    p5$2 := (if !v26$2 then !v26$2 else p5$2);
    v27$1 := (if p0$1 then $$acc$1bv32$1 else v27$1);
    v27$2 := (if p0$2 then $$acc$1bv32$2 else v27$2);
    v28$1 := (if p0$1 then $$res1$1bv32$1 else v28$1);
    v28$2 := (if p0$2 then $$res1$1bv32$2 else v28$2);
    v29$1 := (if p0$1 then BV8_SEXT32(v27$1) == BV8_SEXT32(v28$1) else v29$1);
    v29$2 := (if p0$2 then BV8_SEXT32(v27$2) == BV8_SEXT32(v28$2) else v29$2);
    p1$1 := (if p0$1 && v29$1 then v29$1 else p1$1);
    p1$2 := (if p0$2 && v29$2 then v29$2 else p1$2);
    p4$1 := (if p0$1 && !v29$1 then !v29$1 else p4$1);
    p4$2 := (if p0$2 && !v29$2 then !v29$2 else p4$2);
    v30$1 := (if p1$1 then $$acc$2bv32$1 else v30$1);
    v30$2 := (if p1$2 then $$acc$2bv32$2 else v30$2);
    v31$1 := (if p1$1 then $$res1$2bv32$1 else v31$1);
    v31$2 := (if p1$2 then $$res1$2bv32$2 else v31$2);
    v32$1 := (if p1$1 then BV8_SEXT32(v30$1) == BV8_SEXT32(v31$1) else v32$1);
    v32$2 := (if p1$2 then BV8_SEXT32(v30$2) == BV8_SEXT32(v31$2) else v32$2);
    p2$1 := (if p1$1 && v32$1 then v32$1 else p2$1);
    p2$2 := (if p1$2 && v32$2 then v32$2 else p2$2);
    p3$1 := (if p1$1 && !v32$1 then !v32$1 else p3$1);
    p3$2 := (if p1$2 && !v32$2 then !v32$2 else p3$2);
    v33$1 := (if p2$1 then $$acc$3bv32$1 else v33$1);
    v33$2 := (if p2$2 then $$acc$3bv32$2 else v33$2);
    v34$1 := (if p2$1 then $$res1$3bv32$1 else v34$1);
    v34$2 := (if p2$2 then $$res1$3bv32$2 else v34$2);
    $0$1 := (if p2$1 then (if BV8_SEXT32(v33$1) == BV8_SEXT32(v34$1) then 1bv1 else 0bv1) else $0$1);
    $0$2 := (if p2$2 then (if BV8_SEXT32(v33$2) == BV8_SEXT32(v34$2) then 1bv1 else 0bv1) else $0$2);
    $0$1 := (if p3$1 then 0bv1 else $0$1);
    $0$2 := (if p3$2 then 0bv1 else $0$2);
    $0$1 := (if p4$1 then 0bv1 else $0$1);
    $0$2 := (if p4$2 then 0bv1 else $0$2);
    $0$1 := (if p5$1 then 0bv1 else $0$1);
    $0$2 := (if p5$2 then 0bv1 else $0$2);
    assert {:sourceloc_num 77} {:thread 1} $0$1 != 0bv1;
    assert {:sourceloc_num 77} {:thread 2} $0$2 != 0bv1;
    v35$1 := $$acc$4bv32$1;
    v35$2 := $$acc$4bv32$2;
    v36$1 := $$res2$0bv32$1;
    v36$2 := $$res2$0bv32$2;
    v37$1 := BV8_SEXT32(v35$1) == BV8_SEXT32(v36$1);
    v37$2 := BV8_SEXT32(v35$2) == BV8_SEXT32(v36$2);
    p6$1 := (if v37$1 then v37$1 else p6$1);
    p6$2 := (if v37$2 then v37$2 else p6$2);
    p11$1 := (if !v37$1 then !v37$1 else p11$1);
    p11$2 := (if !v37$2 then !v37$2 else p11$2);
    v38$1 := (if p6$1 then $$acc$5bv32$1 else v38$1);
    v38$2 := (if p6$2 then $$acc$5bv32$2 else v38$2);
    v39$1 := (if p6$1 then $$res2$1bv32$1 else v39$1);
    v39$2 := (if p6$2 then $$res2$1bv32$2 else v39$2);
    v40$1 := (if p6$1 then BV8_SEXT32(v38$1) == BV8_SEXT32(v39$1) else v40$1);
    v40$2 := (if p6$2 then BV8_SEXT32(v38$2) == BV8_SEXT32(v39$2) else v40$2);
    p7$1 := (if p6$1 && v40$1 then v40$1 else p7$1);
    p7$2 := (if p6$2 && v40$2 then v40$2 else p7$2);
    p10$1 := (if p6$1 && !v40$1 then !v40$1 else p10$1);
    p10$2 := (if p6$2 && !v40$2 then !v40$2 else p10$2);
    v41$1 := (if p7$1 then $$acc$6bv32$1 else v41$1);
    v41$2 := (if p7$2 then $$acc$6bv32$2 else v41$2);
    v42$1 := (if p7$1 then $$res2$2bv32$1 else v42$1);
    v42$2 := (if p7$2 then $$res2$2bv32$2 else v42$2);
    v43$1 := (if p7$1 then BV8_SEXT32(v41$1) == BV8_SEXT32(v42$1) else v43$1);
    v43$2 := (if p7$2 then BV8_SEXT32(v41$2) == BV8_SEXT32(v42$2) else v43$2);
    p8$1 := (if p7$1 && v43$1 then v43$1 else p8$1);
    p8$2 := (if p7$2 && v43$2 then v43$2 else p8$2);
    p9$1 := (if p7$1 && !v43$1 then !v43$1 else p9$1);
    p9$2 := (if p7$2 && !v43$2 then !v43$2 else p9$2);
    v44$1 := (if p8$1 then $$acc$7bv32$1 else v44$1);
    v44$2 := (if p8$2 then $$acc$7bv32$2 else v44$2);
    v45$1 := (if p8$1 then $$res2$3bv32$1 else v45$1);
    v45$2 := (if p8$2 then $$res2$3bv32$2 else v45$2);
    $1$1 := (if p8$1 then (if BV8_SEXT32(v44$1) == BV8_SEXT32(v45$1) then 1bv1 else 0bv1) else $1$1);
    $1$2 := (if p8$2 then (if BV8_SEXT32(v44$2) == BV8_SEXT32(v45$2) then 1bv1 else 0bv1) else $1$2);
    $1$1 := (if p9$1 then 0bv1 else $1$1);
    $1$2 := (if p9$2 then 0bv1 else $1$2);
    $1$1 := (if p10$1 then 0bv1 else $1$1);
    $1$2 := (if p10$2 then 0bv1 else $1$2);
    $1$1 := (if p11$1 then 0bv1 else $1$1);
    $1$2 := (if p11$2 then 0bv1 else $1$2);
    assert {:sourceloc_num 90} {:thread 1} $1$1 != 0bv1;
    assert {:sourceloc_num 90} {:thread 2} $1$2 != 0bv1;
    v46$1 := $$acc$8bv32$1;
    v46$2 := $$acc$8bv32$2;
    v47$1 := $$res3$0bv32$1;
    v47$2 := $$res3$0bv32$2;
    v48$1 := BV8_SEXT32(v46$1) == BV8_SEXT32(v47$1);
    v48$2 := BV8_SEXT32(v46$2) == BV8_SEXT32(v47$2);
    p12$1 := (if v48$1 then v48$1 else p12$1);
    p12$2 := (if v48$2 then v48$2 else p12$2);
    p17$1 := (if !v48$1 then !v48$1 else p17$1);
    p17$2 := (if !v48$2 then !v48$2 else p17$2);
    v49$1 := (if p12$1 then $$acc$9bv32$1 else v49$1);
    v49$2 := (if p12$2 then $$acc$9bv32$2 else v49$2);
    v50$1 := (if p12$1 then $$res3$1bv32$1 else v50$1);
    v50$2 := (if p12$2 then $$res3$1bv32$2 else v50$2);
    v51$1 := (if p12$1 then BV8_SEXT32(v49$1) == BV8_SEXT32(v50$1) else v51$1);
    v51$2 := (if p12$2 then BV8_SEXT32(v49$2) == BV8_SEXT32(v50$2) else v51$2);
    p13$1 := (if p12$1 && v51$1 then v51$1 else p13$1);
    p13$2 := (if p12$2 && v51$2 then v51$2 else p13$2);
    p16$1 := (if p12$1 && !v51$1 then !v51$1 else p16$1);
    p16$2 := (if p12$2 && !v51$2 then !v51$2 else p16$2);
    v52$1 := (if p13$1 then $$acc$10bv32$1 else v52$1);
    v52$2 := (if p13$2 then $$acc$10bv32$2 else v52$2);
    v53$1 := (if p13$1 then $$res3$2bv32$1 else v53$1);
    v53$2 := (if p13$2 then $$res3$2bv32$2 else v53$2);
    v54$1 := (if p13$1 then BV8_SEXT32(v52$1) == BV8_SEXT32(v53$1) else v54$1);
    v54$2 := (if p13$2 then BV8_SEXT32(v52$2) == BV8_SEXT32(v53$2) else v54$2);
    p14$1 := (if p13$1 && v54$1 then v54$1 else p14$1);
    p14$2 := (if p13$2 && v54$2 then v54$2 else p14$2);
    p15$1 := (if p13$1 && !v54$1 then !v54$1 else p15$1);
    p15$2 := (if p13$2 && !v54$2 then !v54$2 else p15$2);
    v55$1 := (if p14$1 then $$acc$11bv32$1 else v55$1);
    v55$2 := (if p14$2 then $$acc$11bv32$2 else v55$2);
    v56$1 := (if p14$1 then $$res3$3bv32$1 else v56$1);
    v56$2 := (if p14$2 then $$res3$3bv32$2 else v56$2);
    $2$1 := (if p14$1 then (if BV8_SEXT32(v55$1) == BV8_SEXT32(v56$1) then 1bv1 else 0bv1) else $2$1);
    $2$2 := (if p14$2 then (if BV8_SEXT32(v55$2) == BV8_SEXT32(v56$2) then 1bv1 else 0bv1) else $2$2);
    $2$1 := (if p15$1 then 0bv1 else $2$1);
    $2$2 := (if p15$2 then 0bv1 else $2$2);
    $2$1 := (if p16$1 then 0bv1 else $2$1);
    $2$2 := (if p16$2 then 0bv1 else $2$2);
    $2$1 := (if p17$1 then 0bv1 else $2$1);
    $2$2 := (if p17$2 then 0bv1 else $2$2);
    assert {:sourceloc_num 103} {:thread 1} $2$1 != 0bv1;
    assert {:sourceloc_num 103} {:thread 2} $2$2 != 0bv1;
    v57$1 := $$acc$12bv32$1;
    v57$2 := $$acc$12bv32$2;
    v58$1 := $$res4$0bv32$1;
    v58$2 := $$res4$0bv32$2;
    v59$1 := BV8_SEXT32(v57$1) == BV8_SEXT32(v58$1);
    v59$2 := BV8_SEXT32(v57$2) == BV8_SEXT32(v58$2);
    p18$1 := (if v59$1 then v59$1 else p18$1);
    p18$2 := (if v59$2 then v59$2 else p18$2);
    p23$1 := (if !v59$1 then !v59$1 else p23$1);
    p23$2 := (if !v59$2 then !v59$2 else p23$2);
    v60$1 := (if p18$1 then $$acc$13bv32$1 else v60$1);
    v60$2 := (if p18$2 then $$acc$13bv32$2 else v60$2);
    v61$1 := (if p18$1 then $$res4$1bv32$1 else v61$1);
    v61$2 := (if p18$2 then $$res4$1bv32$2 else v61$2);
    v62$1 := (if p18$1 then BV8_SEXT32(v60$1) == BV8_SEXT32(v61$1) else v62$1);
    v62$2 := (if p18$2 then BV8_SEXT32(v60$2) == BV8_SEXT32(v61$2) else v62$2);
    p19$1 := (if p18$1 && v62$1 then v62$1 else p19$1);
    p19$2 := (if p18$2 && v62$2 then v62$2 else p19$2);
    p22$1 := (if p18$1 && !v62$1 then !v62$1 else p22$1);
    p22$2 := (if p18$2 && !v62$2 then !v62$2 else p22$2);
    v63$1 := (if p19$1 then $$acc$14bv32$1 else v63$1);
    v63$2 := (if p19$2 then $$acc$14bv32$2 else v63$2);
    v64$1 := (if p19$1 then $$res4$2bv32$1 else v64$1);
    v64$2 := (if p19$2 then $$res4$2bv32$2 else v64$2);
    v65$1 := (if p19$1 then BV8_SEXT32(v63$1) == BV8_SEXT32(v64$1) else v65$1);
    v65$2 := (if p19$2 then BV8_SEXT32(v63$2) == BV8_SEXT32(v64$2) else v65$2);
    p20$1 := (if p19$1 && v65$1 then v65$1 else p20$1);
    p20$2 := (if p19$2 && v65$2 then v65$2 else p20$2);
    p21$1 := (if p19$1 && !v65$1 then !v65$1 else p21$1);
    p21$2 := (if p19$2 && !v65$2 then !v65$2 else p21$2);
    v66$1 := (if p20$1 then $$acc$15bv32$1 else v66$1);
    v66$2 := (if p20$2 then $$acc$15bv32$2 else v66$2);
    v67$1 := (if p20$1 then $$res4$3bv32$1 else v67$1);
    v67$2 := (if p20$2 then $$res4$3bv32$2 else v67$2);
    $3$1 := (if p20$1 then (if BV8_SEXT32(v66$1) == BV8_SEXT32(v67$1) then 1bv1 else 0bv1) else $3$1);
    $3$2 := (if p20$2 then (if BV8_SEXT32(v66$2) == BV8_SEXT32(v67$2) then 1bv1 else 0bv1) else $3$2);
    $3$1 := (if p21$1 then 0bv1 else $3$1);
    $3$2 := (if p21$2 then 0bv1 else $3$2);
    $3$1 := (if p22$1 then 0bv1 else $3$1);
    $3$2 := (if p22$2 then 0bv1 else $3$2);
    $3$1 := (if p23$1 then 0bv1 else $3$1);
    $3$2 := (if p23$2 then 0bv1 else $3$2);
    assert {:sourceloc_num 116} {:thread 1} $3$1 != 0bv1;
    assert {:sourceloc_num 116} {:thread 2} $3$2 != 0bv1;
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

var $$acc$0bv32$1: bv8;

var $$acc$0bv32$2: bv8;

var $$acc$1bv32$1: bv8;

var $$acc$1bv32$2: bv8;

var $$acc$2bv32$1: bv8;

var $$acc$2bv32$2: bv8;

var $$acc$3bv32$1: bv8;

var $$acc$3bv32$2: bv8;

var $$acc$4bv32$1: bv8;

var $$acc$4bv32$2: bv8;

var $$acc$5bv32$1: bv8;

var $$acc$5bv32$2: bv8;

var $$acc$6bv32$1: bv8;

var $$acc$6bv32$2: bv8;

var $$acc$7bv32$1: bv8;

var $$acc$7bv32$2: bv8;

var $$acc$8bv32$1: bv8;

var $$acc$8bv32$2: bv8;

var $$acc$9bv32$1: bv8;

var $$acc$9bv32$2: bv8;

var $$acc$10bv32$1: bv8;

var $$acc$10bv32$2: bv8;

var $$acc$11bv32$1: bv8;

var $$acc$11bv32$2: bv8;

var $$acc$12bv32$1: bv8;

var $$acc$12bv32$2: bv8;

var $$acc$13bv32$1: bv8;

var $$acc$13bv32$2: bv8;

var $$acc$14bv32$1: bv8;

var $$acc$14bv32$2: bv8;

var $$acc$15bv32$1: bv8;

var $$acc$15bv32$2: bv8;

var $$res1$0bv32$1: bv8;

var $$res1$0bv32$2: bv8;

var $$res1$1bv32$1: bv8;

var $$res1$1bv32$2: bv8;

var $$res1$2bv32$1: bv8;

var $$res1$2bv32$2: bv8;

var $$res1$3bv32$1: bv8;

var $$res1$3bv32$2: bv8;

var $$res2$0bv32$1: bv8;

var $$res2$0bv32$2: bv8;

var $$res2$1bv32$1: bv8;

var $$res2$1bv32$2: bv8;

var $$res2$2bv32$1: bv8;

var $$res2$2bv32$2: bv8;

var $$res2$3bv32$1: bv8;

var $$res2$3bv32$2: bv8;

var $$res3$0bv32$1: bv8;

var $$res3$0bv32$2: bv8;

var $$res3$1bv32$1: bv8;

var $$res3$1bv32$2: bv8;

var $$res3$2bv32$1: bv8;

var $$res3$2bv32$2: bv8;

var $$res3$3bv32$1: bv8;

var $$res3$3bv32$2: bv8;

var $$res4$0bv32$1: bv8;

var $$res4$0bv32$2: bv8;

var $$res4$1bv32$1: bv8;

var $$res4$1bv32$2: bv8;

var $$res4$2bv32$1: bv8;

var $$res4$2bv32$2: bv8;

var $$res4$3bv32$1: bv8;

var $$res4$3bv32$2: bv8;

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
