//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP64(x: [bv32]bv64, y: bv32) returns (z$1: bv64, A$1: [bv32]bv64, z$2: bv64, A$2: [bv32]bv64);

procedure _ATOMIC_OP8(x: [bv32]bv8, y: bv32) returns (z$1: bv8, A$1: [bv32]bv8, z$2: bv8, A$2: [bv32]bv8);

var {:source_name "p"} {:global} $$p: [bv32]bv64;

axiom {:array_info "$$p"} {:global} {:elem_width 64} {:source_name "p"} {:source_elem_width 256} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 64} {:source_elem_width 256} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$p: bool;

var {:race_checking} {:global} {:elem_width 64} {:source_elem_width 256} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$p: bool;

var {:race_checking} {:global} {:elem_width 64} {:source_elem_width 256} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$p: bool;

axiom {:array_info "$$w"} {:elem_width 8} {:source_name "w"} {:source_elem_width 256} {:source_dimensions "1"} true;

axiom {:array_info "$$v2x"} {:elem_width 8} {:source_name "v2x"} {:source_elem_width 64} {:source_dimensions "1"} true;

axiom {:array_info "$$v2y"} {:elem_width 8} {:source_name "v2y"} {:source_elem_width 64} {:source_dimensions "1"} true;

axiom {:array_info "$$v2z"} {:elem_width 8} {:source_name "v2z"} {:source_elem_width 64} {:source_dimensions "1"} true;

axiom {:array_info "$$v2w"} {:elem_width 8} {:source_name "v2w"} {:source_elem_width 64} {:source_dimensions "1"} true;

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

function FADD64(bv64, bv64) : bv64;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

function {:builtin "sign_extend 24"} BV8_SEXT32(bv8) : bv32;

procedure {:source_name "foo"} ULTIMATE.start();
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
  modifies _READ_HAS_OCCURRED_$$p, _WRITE_HAS_OCCURRED_$$p, _WRITE_READ_BENIGN_FLAG_$$p, _WRITE_READ_BENIGN_FLAG_$$p;

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
  var v4$1: bv64;
  var v4$2: bv64;
  var v5$1: bv64;
  var v5$2: bv64;
  var v0$1: bv64;
  var v0$2: bv64;
  var v1$1: bv64;
  var v1$2: bv64;
  var v2$1: bv64;
  var v2$2: bv64;
  var v3$1: bv64;
  var v3$2: bv64;
  var v6$1: bv64;
  var v6$2: bv64;
  var v7$1: bv64;
  var v7$2: bv64;
  var v8$1: bv64;
  var v8$2: bv64;
  var v9$1: bv64;
  var v9$2: bv64;
  var v10$1: bv64;
  var v10$2: bv64;
  var v11$1: bv64;
  var v11$2: bv64;
  var v12$1: bv8;
  var v12$2: bv8;
  var v13$1: bv8;
  var v13$2: bv8;
  var v14$1: bool;
  var v14$2: bool;
  var v15$1: bv8;
  var v15$2: bv8;
  var v16$1: bv8;
  var v16$2: bv8;
  var v17$1: bool;
  var v17$2: bool;
  var v18$1: bv8;
  var v18$2: bv8;
  var v19$1: bv8;
  var v19$2: bv8;
  var v20$1: bool;
  var v20$2: bool;
  var v21$1: bv8;
  var v21$2: bv8;
  var v22$1: bv8;
  var v22$2: bv8;
  var v23$1: bool;
  var v23$2: bool;
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
  var v46$1: bool;
  var v46$2: bool;
  var v47$1: bv8;
  var v47$2: bv8;
  var v48$1: bv8;
  var v48$2: bv8;
  var v49$1: bool;
  var v49$2: bool;
  var v50$1: bv8;
  var v50$2: bv8;
  var v61$1: bv8;
  var v61$2: bv8;
  var v62$1: bv8;
  var v62$2: bv8;
  var v63$1: bool;
  var v63$2: bool;
  var v64$1: bv8;
  var v64$2: bv8;
  var v65$1: bv8;
  var v65$2: bv8;
  var v66$1: bool;
  var v66$2: bool;
  var v67$1: bv8;
  var v67$2: bv8;
  var v68$1: bv8;
  var v68$2: bv8;
  var v69$1: bool;
  var v69$2: bool;
  var v70$1: bv8;
  var v70$2: bv8;
  var v71$1: bv8;
  var v71$2: bv8;
  var v72$1: bool;
  var v72$2: bool;
  var v73$1: bv8;
  var v73$2: bv8;
  var v74$1: bv8;
  var v74$2: bv8;
  var v75$1: bool;
  var v75$2: bool;
  var v76$1: bv8;
  var v76$2: bv8;
  var v77$1: bv8;
  var v77$2: bv8;
  var v78$1: bool;
  var v78$2: bool;
  var v79$1: bv8;
  var v79$2: bv8;
  var v80$1: bv8;
  var v80$2: bv8;
  var v81$1: bv8;
  var v81$2: bv8;
  var v82$1: bv8;
  var v82$2: bv8;
  var v83$1: bool;
  var v83$2: bool;
  var v84$1: bv8;
  var v84$2: bv8;
  var v85$1: bv8;
  var v85$2: bv8;
  var v86$1: bool;
  var v86$2: bool;
  var v87$1: bv8;
  var v87$2: bv8;
  var v88$1: bv8;
  var v88$2: bv8;
  var v89$1: bool;
  var v89$2: bool;
  var v90$1: bv8;
  var v90$2: bv8;
  var v91$1: bv8;
  var v91$2: bv8;
  var v92$1: bool;
  var v92$2: bool;
  var v93$1: bv8;
  var v93$2: bv8;
  var v94$1: bv8;
  var v94$2: bv8;
  var v95$1: bool;
  var v95$2: bool;
  var v96$1: bv8;
  var v96$2: bv8;
  var v97$1: bv8;
  var v97$2: bv8;
  var v98$1: bool;
  var v98$2: bool;
  var v99$1: bv8;
  var v99$2: bv8;
  var v100$1: bv8;
  var v100$2: bv8;
  var v101$1: bool;
  var v101$2: bool;
  var v102$1: bv8;
  var v102$2: bv8;
  var v103$1: bv8;
  var v103$2: bv8;
  var v105$1: bv8;
  var v105$2: bv8;
  var v104$1: bv8;
  var v104$2: bv8;
  var v106$1: bv8;
  var v106$2: bv8;
  var v107$1: bv8;
  var v107$2: bv8;
  var v108$1: bv8;
  var v108$2: bv8;
  var v109$1: bv8;
  var v109$2: bv8;
  var v110$1: bv8;
  var v110$2: bv8;
  var v121$1: bv8;
  var v121$2: bv8;
  var v111$1: bv8;
  var v111$2: bv8;
  var v112$1: bv8;
  var v112$2: bv8;
  var v113$1: bv8;
  var v113$2: bv8;
  var v114$1: bv8;
  var v114$2: bv8;
  var v115$1: bv8;
  var v115$2: bv8;
  var v116$1: bv8;
  var v116$2: bv8;
  var v117$1: bv8;
  var v117$2: bv8;
  var v118$1: bv8;
  var v118$2: bv8;
  var v135$1: bv8;
  var v135$2: bv8;
  var v119$1: bv8;
  var v119$2: bv8;
  var v120$1: bv8;
  var v120$2: bv8;
  var v122$1: bv8;
  var v122$2: bv8;
  var v123$1: bv8;
  var v123$2: bv8;
  var v124$1: bv8;
  var v124$2: bv8;
  var v125$1: bv8;
  var v125$2: bv8;
  var v126$1: bv8;
  var v126$2: bv8;
  var v127$1: bv8;
  var v127$2: bv8;
  var v128$1: bv8;
  var v128$2: bv8;
  var v129$1: bv8;
  var v129$2: bv8;
  var v130$1: bv8;
  var v130$2: bv8;
  var v131$1: bv8;
  var v131$2: bv8;
  var v132$1: bv8;
  var v132$2: bv8;
  var v133$1: bv8;
  var v133$2: bv8;
  var v134$1: bv8;
  var v134$2: bv8;
  var v51$1: bv8;
  var v51$2: bv8;
  var v52$1: bool;
  var v52$2: bool;
  var v53$1: bv8;
  var v53$2: bv8;
  var v54$1: bv8;
  var v54$2: bv8;
  var v55$1: bool;
  var v55$2: bool;
  var v56$1: bv8;
  var v56$2: bv8;
  var v57$1: bv8;
  var v57$2: bv8;
  var v58$1: bv8;
  var v58$2: bv8;
  var v59$1: bv8;
  var v59$2: bv8;
  var v60$1: bool;
  var v60$2: bool;
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

  $entry:
    call _LOG_READ_$$p(true, BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), $$p[BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 1} true;
    call _CHECK_READ_$$p(true, BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), $$p[BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$p"} true;
    v0$1 := $$p[BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32)];
    v0$2 := $$p[BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32)];
    call _LOG_READ_$$p(true, BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 1bv32), $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 1bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 2} true;
    call _CHECK_READ_$$p(true, BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 1bv32), $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 1bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$p"} true;
    v1$1 := $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 1bv32)];
    v1$2 := $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 1bv32)];
    call _LOG_READ_$$p(true, BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 2bv32), $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 2bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 3} true;
    call _CHECK_READ_$$p(true, BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 2bv32), $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 2bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$p"} true;
    v2$1 := $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 2bv32)];
    v2$2 := $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 2bv32)];
    call _LOG_READ_$$p(true, BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 3bv32), $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 3bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 4} true;
    call _CHECK_READ_$$p(true, BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 3bv32), $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 3bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$p"} true;
    v3$1 := $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 3bv32)];
    v3$2 := $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 3bv32)];
    v4$1 := FADD64(v0$1, v0$1);
    v4$2 := FADD64(v0$2, v0$2);
    v5$1 := FADD64(v1$1, v1$1);
    v5$2 := FADD64(v1$2, v1$2);
    v6$1 := FADD64(v2$1, v2$1);
    v6$2 := FADD64(v2$2, v2$2);
    v7$1 := FADD64(v3$1, v3$1);
    v7$2 := FADD64(v3$2, v3$2);
    $$w$0bv32$1 := v4$1[8:0];
    $$w$0bv32$2 := v4$2[8:0];
    $$w$1bv32$1 := v4$1[16:8];
    $$w$1bv32$2 := v4$2[16:8];
    $$w$2bv32$1 := v4$1[24:16];
    $$w$2bv32$2 := v4$2[24:16];
    $$w$3bv32$1 := v4$1[32:24];
    $$w$3bv32$2 := v4$2[32:24];
    $$w$4bv32$1 := v4$1[40:32];
    $$w$4bv32$2 := v4$2[40:32];
    $$w$5bv32$1 := v4$1[48:40];
    $$w$5bv32$2 := v4$2[48:40];
    $$w$6bv32$1 := v4$1[56:48];
    $$w$6bv32$2 := v4$2[56:48];
    $$w$7bv32$1 := v4$1[64:56];
    $$w$7bv32$2 := v4$2[64:56];
    $$w$8bv32$1 := v5$1[8:0];
    $$w$8bv32$2 := v5$2[8:0];
    $$w$9bv32$1 := v5$1[16:8];
    $$w$9bv32$2 := v5$2[16:8];
    $$w$10bv32$1 := v5$1[24:16];
    $$w$10bv32$2 := v5$2[24:16];
    $$w$11bv32$1 := v5$1[32:24];
    $$w$11bv32$2 := v5$2[32:24];
    $$w$12bv32$1 := v5$1[40:32];
    $$w$12bv32$2 := v5$2[40:32];
    $$w$13bv32$1 := v5$1[48:40];
    $$w$13bv32$2 := v5$2[48:40];
    $$w$14bv32$1 := v5$1[56:48];
    $$w$14bv32$2 := v5$2[56:48];
    $$w$15bv32$1 := v5$1[64:56];
    $$w$15bv32$2 := v5$2[64:56];
    $$w$16bv32$1 := v6$1[8:0];
    $$w$16bv32$2 := v6$2[8:0];
    $$w$17bv32$1 := v6$1[16:8];
    $$w$17bv32$2 := v6$2[16:8];
    $$w$18bv32$1 := v6$1[24:16];
    $$w$18bv32$2 := v6$2[24:16];
    $$w$19bv32$1 := v6$1[32:24];
    $$w$19bv32$2 := v6$2[32:24];
    $$w$20bv32$1 := v6$1[40:32];
    $$w$20bv32$2 := v6$2[40:32];
    $$w$21bv32$1 := v6$1[48:40];
    $$w$21bv32$2 := v6$2[48:40];
    $$w$22bv32$1 := v6$1[56:48];
    $$w$22bv32$2 := v6$2[56:48];
    $$w$23bv32$1 := v6$1[64:56];
    $$w$23bv32$2 := v6$2[64:56];
    $$w$24bv32$1 := v7$1[8:0];
    $$w$24bv32$2 := v7$2[8:0];
    $$w$25bv32$1 := v7$1[16:8];
    $$w$25bv32$2 := v7$2[16:8];
    $$w$26bv32$1 := v7$1[24:16];
    $$w$26bv32$2 := v7$2[24:16];
    $$w$27bv32$1 := v7$1[32:24];
    $$w$27bv32$2 := v7$2[32:24];
    $$w$28bv32$1 := v7$1[40:32];
    $$w$28bv32$2 := v7$2[40:32];
    $$w$29bv32$1 := v7$1[48:40];
    $$w$29bv32$2 := v7$2[48:40];
    $$w$30bv32$1 := v7$1[56:48];
    $$w$30bv32$2 := v7$2[56:48];
    $$w$31bv32$1 := v7$1[64:56];
    $$w$31bv32$2 := v7$2[64:56];
    v8$1 := FADD64(v0$1, v0$1);
    v8$2 := FADD64(v0$2, v0$2);
    $$v2x$0bv32$1 := v8$1[8:0];
    $$v2x$0bv32$2 := v8$2[8:0];
    $$v2x$1bv32$1 := v8$1[16:8];
    $$v2x$1bv32$2 := v8$2[16:8];
    $$v2x$2bv32$1 := v8$1[24:16];
    $$v2x$2bv32$2 := v8$2[24:16];
    $$v2x$3bv32$1 := v8$1[32:24];
    $$v2x$3bv32$2 := v8$2[32:24];
    $$v2x$4bv32$1 := v8$1[40:32];
    $$v2x$4bv32$2 := v8$2[40:32];
    $$v2x$5bv32$1 := v8$1[48:40];
    $$v2x$5bv32$2 := v8$2[48:40];
    $$v2x$6bv32$1 := v8$1[56:48];
    $$v2x$6bv32$2 := v8$2[56:48];
    $$v2x$7bv32$1 := v8$1[64:56];
    $$v2x$7bv32$2 := v8$2[64:56];
    v9$1 := FADD64(v1$1, v1$1);
    v9$2 := FADD64(v1$2, v1$2);
    $$v2y$0bv32$1 := v9$1[8:0];
    $$v2y$0bv32$2 := v9$2[8:0];
    $$v2y$1bv32$1 := v9$1[16:8];
    $$v2y$1bv32$2 := v9$2[16:8];
    $$v2y$2bv32$1 := v9$1[24:16];
    $$v2y$2bv32$2 := v9$2[24:16];
    $$v2y$3bv32$1 := v9$1[32:24];
    $$v2y$3bv32$2 := v9$2[32:24];
    $$v2y$4bv32$1 := v9$1[40:32];
    $$v2y$4bv32$2 := v9$2[40:32];
    $$v2y$5bv32$1 := v9$1[48:40];
    $$v2y$5bv32$2 := v9$2[48:40];
    $$v2y$6bv32$1 := v9$1[56:48];
    $$v2y$6bv32$2 := v9$2[56:48];
    $$v2y$7bv32$1 := v9$1[64:56];
    $$v2y$7bv32$2 := v9$2[64:56];
    v10$1 := FADD64(v2$1, v2$1);
    v10$2 := FADD64(v2$2, v2$2);
    $$v2z$0bv32$1 := v10$1[8:0];
    $$v2z$0bv32$2 := v10$2[8:0];
    $$v2z$1bv32$1 := v10$1[16:8];
    $$v2z$1bv32$2 := v10$2[16:8];
    $$v2z$2bv32$1 := v10$1[24:16];
    $$v2z$2bv32$2 := v10$2[24:16];
    $$v2z$3bv32$1 := v10$1[32:24];
    $$v2z$3bv32$2 := v10$2[32:24];
    $$v2z$4bv32$1 := v10$1[40:32];
    $$v2z$4bv32$2 := v10$2[40:32];
    $$v2z$5bv32$1 := v10$1[48:40];
    $$v2z$5bv32$2 := v10$2[48:40];
    $$v2z$6bv32$1 := v10$1[56:48];
    $$v2z$6bv32$2 := v10$2[56:48];
    $$v2z$7bv32$1 := v10$1[64:56];
    $$v2z$7bv32$2 := v10$2[64:56];
    v11$1 := FADD64(v3$1, v3$1);
    v11$2 := FADD64(v3$2, v3$2);
    $$v2w$0bv32$1 := v11$1[8:0];
    $$v2w$0bv32$2 := v11$2[8:0];
    $$v2w$1bv32$1 := v11$1[16:8];
    $$v2w$1bv32$2 := v11$2[16:8];
    $$v2w$2bv32$1 := v11$1[24:16];
    $$v2w$2bv32$2 := v11$2[24:16];
    $$v2w$3bv32$1 := v11$1[32:24];
    $$v2w$3bv32$2 := v11$2[32:24];
    $$v2w$4bv32$1 := v11$1[40:32];
    $$v2w$4bv32$2 := v11$2[40:32];
    $$v2w$5bv32$1 := v11$1[48:40];
    $$v2w$5bv32$2 := v11$2[48:40];
    $$v2w$6bv32$1 := v11$1[56:48];
    $$v2w$6bv32$2 := v11$2[56:48];
    $$v2w$7bv32$1 := v11$1[64:56];
    $$v2w$7bv32$2 := v11$2[64:56];
    v12$1 := $$w$0bv32$1;
    v12$2 := $$w$0bv32$2;
    v13$1 := $$v2x$0bv32$1;
    v13$2 := $$v2x$0bv32$2;
    v14$1 := BV8_SEXT32(v12$1) == BV8_SEXT32(v13$1);
    v14$2 := BV8_SEXT32(v12$2) == BV8_SEXT32(v13$2);
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
    p0$1 := (if v14$1 then v14$1 else p0$1);
    p0$2 := (if v14$2 then v14$2 else p0$2);
    p13$1 := (if !v14$1 then !v14$1 else p13$1);
    p13$2 := (if !v14$2 then !v14$2 else p13$2);
    v15$1 := (if p0$1 then $$w$1bv32$1 else v15$1);
    v15$2 := (if p0$2 then $$w$1bv32$2 else v15$2);
    v16$1 := (if p0$1 then $$v2x$1bv32$1 else v16$1);
    v16$2 := (if p0$2 then $$v2x$1bv32$2 else v16$2);
    v17$1 := (if p0$1 then BV8_SEXT32(v15$1) == BV8_SEXT32(v16$1) else v17$1);
    v17$2 := (if p0$2 then BV8_SEXT32(v15$2) == BV8_SEXT32(v16$2) else v17$2);
    p1$1 := (if p0$1 && v17$1 then v17$1 else p1$1);
    p1$2 := (if p0$2 && v17$2 then v17$2 else p1$2);
    p12$1 := (if p0$1 && !v17$1 then !v17$1 else p12$1);
    p12$2 := (if p0$2 && !v17$2 then !v17$2 else p12$2);
    v18$1 := (if p1$1 then $$w$2bv32$1 else v18$1);
    v18$2 := (if p1$2 then $$w$2bv32$2 else v18$2);
    v19$1 := (if p1$1 then $$v2x$2bv32$1 else v19$1);
    v19$2 := (if p1$2 then $$v2x$2bv32$2 else v19$2);
    v20$1 := (if p1$1 then BV8_SEXT32(v18$1) == BV8_SEXT32(v19$1) else v20$1);
    v20$2 := (if p1$2 then BV8_SEXT32(v18$2) == BV8_SEXT32(v19$2) else v20$2);
    p2$1 := (if p1$1 && v20$1 then v20$1 else p2$1);
    p2$2 := (if p1$2 && v20$2 then v20$2 else p2$2);
    p11$1 := (if p1$1 && !v20$1 then !v20$1 else p11$1);
    p11$2 := (if p1$2 && !v20$2 then !v20$2 else p11$2);
    v21$1 := (if p2$1 then $$w$3bv32$1 else v21$1);
    v21$2 := (if p2$2 then $$w$3bv32$2 else v21$2);
    v22$1 := (if p2$1 then $$v2x$3bv32$1 else v22$1);
    v22$2 := (if p2$2 then $$v2x$3bv32$2 else v22$2);
    v23$1 := (if p2$1 then BV8_SEXT32(v21$1) == BV8_SEXT32(v22$1) else v23$1);
    v23$2 := (if p2$2 then BV8_SEXT32(v21$2) == BV8_SEXT32(v22$2) else v23$2);
    p3$1 := (if p2$1 && v23$1 then v23$1 else p3$1);
    p3$2 := (if p2$2 && v23$2 then v23$2 else p3$2);
    p10$1 := (if p2$1 && !v23$1 then !v23$1 else p10$1);
    p10$2 := (if p2$2 && !v23$2 then !v23$2 else p10$2);
    v24$1 := (if p3$1 then $$w$4bv32$1 else v24$1);
    v24$2 := (if p3$2 then $$w$4bv32$2 else v24$2);
    v25$1 := (if p3$1 then $$v2x$4bv32$1 else v25$1);
    v25$2 := (if p3$2 then $$v2x$4bv32$2 else v25$2);
    v26$1 := (if p3$1 then BV8_SEXT32(v24$1) == BV8_SEXT32(v25$1) else v26$1);
    v26$2 := (if p3$2 then BV8_SEXT32(v24$2) == BV8_SEXT32(v25$2) else v26$2);
    p4$1 := (if p3$1 && v26$1 then v26$1 else p4$1);
    p4$2 := (if p3$2 && v26$2 then v26$2 else p4$2);
    p9$1 := (if p3$1 && !v26$1 then !v26$1 else p9$1);
    p9$2 := (if p3$2 && !v26$2 then !v26$2 else p9$2);
    v27$1 := (if p4$1 then $$w$5bv32$1 else v27$1);
    v27$2 := (if p4$2 then $$w$5bv32$2 else v27$2);
    v28$1 := (if p4$1 then $$v2x$5bv32$1 else v28$1);
    v28$2 := (if p4$2 then $$v2x$5bv32$2 else v28$2);
    v29$1 := (if p4$1 then BV8_SEXT32(v27$1) == BV8_SEXT32(v28$1) else v29$1);
    v29$2 := (if p4$2 then BV8_SEXT32(v27$2) == BV8_SEXT32(v28$2) else v29$2);
    p5$1 := (if p4$1 && v29$1 then v29$1 else p5$1);
    p5$2 := (if p4$2 && v29$2 then v29$2 else p5$2);
    p8$1 := (if p4$1 && !v29$1 then !v29$1 else p8$1);
    p8$2 := (if p4$2 && !v29$2 then !v29$2 else p8$2);
    v30$1 := (if p5$1 then $$w$6bv32$1 else v30$1);
    v30$2 := (if p5$2 then $$w$6bv32$2 else v30$2);
    v31$1 := (if p5$1 then $$v2x$6bv32$1 else v31$1);
    v31$2 := (if p5$2 then $$v2x$6bv32$2 else v31$2);
    v32$1 := (if p5$1 then BV8_SEXT32(v30$1) == BV8_SEXT32(v31$1) else v32$1);
    v32$2 := (if p5$2 then BV8_SEXT32(v30$2) == BV8_SEXT32(v31$2) else v32$2);
    p6$1 := (if p5$1 && v32$1 then v32$1 else p6$1);
    p6$2 := (if p5$2 && v32$2 then v32$2 else p6$2);
    p7$1 := (if p5$1 && !v32$1 then !v32$1 else p7$1);
    p7$2 := (if p5$2 && !v32$2 then !v32$2 else p7$2);
    v33$1 := (if p6$1 then $$w$7bv32$1 else v33$1);
    v33$2 := (if p6$2 then $$w$7bv32$2 else v33$2);
    v34$1 := (if p6$1 then $$v2x$7bv32$1 else v34$1);
    v34$2 := (if p6$2 then $$v2x$7bv32$2 else v34$2);
    $0$1 := (if p6$1 then (if BV8_SEXT32(v33$1) == BV8_SEXT32(v34$1) then 1bv1 else 0bv1) else $0$1);
    $0$2 := (if p6$2 then (if BV8_SEXT32(v33$2) == BV8_SEXT32(v34$2) then 1bv1 else 0bv1) else $0$2);
    $0$1 := (if p7$1 then 0bv1 else $0$1);
    $0$2 := (if p7$2 then 0bv1 else $0$2);
    $0$1 := (if p8$1 then 0bv1 else $0$1);
    $0$2 := (if p8$2 then 0bv1 else $0$2);
    $0$1 := (if p9$1 then 0bv1 else $0$1);
    $0$2 := (if p9$2 then 0bv1 else $0$2);
    $0$1 := (if p10$1 then 0bv1 else $0$1);
    $0$2 := (if p10$2 then 0bv1 else $0$2);
    $0$1 := (if p11$1 then 0bv1 else $0$1);
    $0$2 := (if p11$2 then 0bv1 else $0$2);
    $0$1 := (if p12$1 then 0bv1 else $0$1);
    $0$2 := (if p12$2 then 0bv1 else $0$2);
    $0$1 := (if p13$1 then 0bv1 else $0$1);
    $0$2 := (if p13$2 then 0bv1 else $0$2);
    assert {:sourceloc_num 93} {:thread 1} $0$1 != 0bv1;
    assert {:sourceloc_num 93} {:thread 2} $0$2 != 0bv1;
    v35$1 := $$w$8bv32$1;
    v35$2 := $$w$8bv32$2;
    v36$1 := $$v2y$0bv32$1;
    v36$2 := $$v2y$0bv32$2;
    v37$1 := BV8_SEXT32(v35$1) == BV8_SEXT32(v36$1);
    v37$2 := BV8_SEXT32(v35$2) == BV8_SEXT32(v36$2);
    p14$1 := (if v37$1 then v37$1 else p14$1);
    p14$2 := (if v37$2 then v37$2 else p14$2);
    p27$1 := (if !v37$1 then !v37$1 else p27$1);
    p27$2 := (if !v37$2 then !v37$2 else p27$2);
    v38$1 := (if p14$1 then $$w$9bv32$1 else v38$1);
    v38$2 := (if p14$2 then $$w$9bv32$2 else v38$2);
    v39$1 := (if p14$1 then $$v2y$1bv32$1 else v39$1);
    v39$2 := (if p14$2 then $$v2y$1bv32$2 else v39$2);
    v40$1 := (if p14$1 then BV8_SEXT32(v38$1) == BV8_SEXT32(v39$1) else v40$1);
    v40$2 := (if p14$2 then BV8_SEXT32(v38$2) == BV8_SEXT32(v39$2) else v40$2);
    p15$1 := (if p14$1 && v40$1 then v40$1 else p15$1);
    p15$2 := (if p14$2 && v40$2 then v40$2 else p15$2);
    p26$1 := (if p14$1 && !v40$1 then !v40$1 else p26$1);
    p26$2 := (if p14$2 && !v40$2 then !v40$2 else p26$2);
    v41$1 := (if p15$1 then $$w$10bv32$1 else v41$1);
    v41$2 := (if p15$2 then $$w$10bv32$2 else v41$2);
    v42$1 := (if p15$1 then $$v2y$2bv32$1 else v42$1);
    v42$2 := (if p15$2 then $$v2y$2bv32$2 else v42$2);
    v43$1 := (if p15$1 then BV8_SEXT32(v41$1) == BV8_SEXT32(v42$1) else v43$1);
    v43$2 := (if p15$2 then BV8_SEXT32(v41$2) == BV8_SEXT32(v42$2) else v43$2);
    p16$1 := (if p15$1 && v43$1 then v43$1 else p16$1);
    p16$2 := (if p15$2 && v43$2 then v43$2 else p16$2);
    p25$1 := (if p15$1 && !v43$1 then !v43$1 else p25$1);
    p25$2 := (if p15$2 && !v43$2 then !v43$2 else p25$2);
    v44$1 := (if p16$1 then $$w$11bv32$1 else v44$1);
    v44$2 := (if p16$2 then $$w$11bv32$2 else v44$2);
    v45$1 := (if p16$1 then $$v2y$3bv32$1 else v45$1);
    v45$2 := (if p16$2 then $$v2y$3bv32$2 else v45$2);
    v46$1 := (if p16$1 then BV8_SEXT32(v44$1) == BV8_SEXT32(v45$1) else v46$1);
    v46$2 := (if p16$2 then BV8_SEXT32(v44$2) == BV8_SEXT32(v45$2) else v46$2);
    p17$1 := (if p16$1 && v46$1 then v46$1 else p17$1);
    p17$2 := (if p16$2 && v46$2 then v46$2 else p17$2);
    p24$1 := (if p16$1 && !v46$1 then !v46$1 else p24$1);
    p24$2 := (if p16$2 && !v46$2 then !v46$2 else p24$2);
    v47$1 := (if p17$1 then $$w$12bv32$1 else v47$1);
    v47$2 := (if p17$2 then $$w$12bv32$2 else v47$2);
    v48$1 := (if p17$1 then $$v2y$4bv32$1 else v48$1);
    v48$2 := (if p17$2 then $$v2y$4bv32$2 else v48$2);
    v49$1 := (if p17$1 then BV8_SEXT32(v47$1) == BV8_SEXT32(v48$1) else v49$1);
    v49$2 := (if p17$2 then BV8_SEXT32(v47$2) == BV8_SEXT32(v48$2) else v49$2);
    p18$1 := (if p17$1 && v49$1 then v49$1 else p18$1);
    p18$2 := (if p17$2 && v49$2 then v49$2 else p18$2);
    p23$1 := (if p17$1 && !v49$1 then !v49$1 else p23$1);
    p23$2 := (if p17$2 && !v49$2 then !v49$2 else p23$2);
    v50$1 := (if p18$1 then $$w$13bv32$1 else v50$1);
    v50$2 := (if p18$2 then $$w$13bv32$2 else v50$2);
    v51$1 := (if p18$1 then $$v2y$5bv32$1 else v51$1);
    v51$2 := (if p18$2 then $$v2y$5bv32$2 else v51$2);
    v52$1 := (if p18$1 then BV8_SEXT32(v50$1) == BV8_SEXT32(v51$1) else v52$1);
    v52$2 := (if p18$2 then BV8_SEXT32(v50$2) == BV8_SEXT32(v51$2) else v52$2);
    p19$1 := (if p18$1 && v52$1 then v52$1 else p19$1);
    p19$2 := (if p18$2 && v52$2 then v52$2 else p19$2);
    p22$1 := (if p18$1 && !v52$1 then !v52$1 else p22$1);
    p22$2 := (if p18$2 && !v52$2 then !v52$2 else p22$2);
    v53$1 := (if p19$1 then $$w$14bv32$1 else v53$1);
    v53$2 := (if p19$2 then $$w$14bv32$2 else v53$2);
    v54$1 := (if p19$1 then $$v2y$6bv32$1 else v54$1);
    v54$2 := (if p19$2 then $$v2y$6bv32$2 else v54$2);
    v55$1 := (if p19$1 then BV8_SEXT32(v53$1) == BV8_SEXT32(v54$1) else v55$1);
    v55$2 := (if p19$2 then BV8_SEXT32(v53$2) == BV8_SEXT32(v54$2) else v55$2);
    p20$1 := (if p19$1 && v55$1 then v55$1 else p20$1);
    p20$2 := (if p19$2 && v55$2 then v55$2 else p20$2);
    p21$1 := (if p19$1 && !v55$1 then !v55$1 else p21$1);
    p21$2 := (if p19$2 && !v55$2 then !v55$2 else p21$2);
    v56$1 := (if p20$1 then $$w$15bv32$1 else v56$1);
    v56$2 := (if p20$2 then $$w$15bv32$2 else v56$2);
    v57$1 := (if p20$1 then $$v2y$7bv32$1 else v57$1);
    v57$2 := (if p20$2 then $$v2y$7bv32$2 else v57$2);
    $1$1 := (if p20$1 then (if BV8_SEXT32(v56$1) == BV8_SEXT32(v57$1) then 1bv1 else 0bv1) else $1$1);
    $1$2 := (if p20$2 then (if BV8_SEXT32(v56$2) == BV8_SEXT32(v57$2) then 1bv1 else 0bv1) else $1$2);
    $1$1 := (if p21$1 then 0bv1 else $1$1);
    $1$2 := (if p21$2 then 0bv1 else $1$2);
    $1$1 := (if p22$1 then 0bv1 else $1$1);
    $1$2 := (if p22$2 then 0bv1 else $1$2);
    $1$1 := (if p23$1 then 0bv1 else $1$1);
    $1$2 := (if p23$2 then 0bv1 else $1$2);
    $1$1 := (if p24$1 then 0bv1 else $1$1);
    $1$2 := (if p24$2 then 0bv1 else $1$2);
    $1$1 := (if p25$1 then 0bv1 else $1$1);
    $1$2 := (if p25$2 then 0bv1 else $1$2);
    $1$1 := (if p26$1 then 0bv1 else $1$1);
    $1$2 := (if p26$2 then 0bv1 else $1$2);
    $1$1 := (if p27$1 then 0bv1 else $1$1);
    $1$2 := (if p27$2 then 0bv1 else $1$2);
    assert {:sourceloc_num 118} {:thread 1} $1$1 != 0bv1;
    assert {:sourceloc_num 118} {:thread 2} $1$2 != 0bv1;
    v58$1 := $$w$16bv32$1;
    v58$2 := $$w$16bv32$2;
    v59$1 := $$v2z$0bv32$1;
    v59$2 := $$v2z$0bv32$2;
    v60$1 := BV8_SEXT32(v58$1) == BV8_SEXT32(v59$1);
    v60$2 := BV8_SEXT32(v58$2) == BV8_SEXT32(v59$2);
    p28$1 := (if v60$1 then v60$1 else p28$1);
    p28$2 := (if v60$2 then v60$2 else p28$2);
    p41$1 := (if !v60$1 then !v60$1 else p41$1);
    p41$2 := (if !v60$2 then !v60$2 else p41$2);
    v61$1 := (if p28$1 then $$w$17bv32$1 else v61$1);
    v61$2 := (if p28$2 then $$w$17bv32$2 else v61$2);
    v62$1 := (if p28$1 then $$v2z$1bv32$1 else v62$1);
    v62$2 := (if p28$2 then $$v2z$1bv32$2 else v62$2);
    v63$1 := (if p28$1 then BV8_SEXT32(v61$1) == BV8_SEXT32(v62$1) else v63$1);
    v63$2 := (if p28$2 then BV8_SEXT32(v61$2) == BV8_SEXT32(v62$2) else v63$2);
    p29$1 := (if p28$1 && v63$1 then v63$1 else p29$1);
    p29$2 := (if p28$2 && v63$2 then v63$2 else p29$2);
    p40$1 := (if p28$1 && !v63$1 then !v63$1 else p40$1);
    p40$2 := (if p28$2 && !v63$2 then !v63$2 else p40$2);
    v64$1 := (if p29$1 then $$w$18bv32$1 else v64$1);
    v64$2 := (if p29$2 then $$w$18bv32$2 else v64$2);
    v65$1 := (if p29$1 then $$v2z$2bv32$1 else v65$1);
    v65$2 := (if p29$2 then $$v2z$2bv32$2 else v65$2);
    v66$1 := (if p29$1 then BV8_SEXT32(v64$1) == BV8_SEXT32(v65$1) else v66$1);
    v66$2 := (if p29$2 then BV8_SEXT32(v64$2) == BV8_SEXT32(v65$2) else v66$2);
    p30$1 := (if p29$1 && v66$1 then v66$1 else p30$1);
    p30$2 := (if p29$2 && v66$2 then v66$2 else p30$2);
    p39$1 := (if p29$1 && !v66$1 then !v66$1 else p39$1);
    p39$2 := (if p29$2 && !v66$2 then !v66$2 else p39$2);
    v67$1 := (if p30$1 then $$w$19bv32$1 else v67$1);
    v67$2 := (if p30$2 then $$w$19bv32$2 else v67$2);
    v68$1 := (if p30$1 then $$v2z$3bv32$1 else v68$1);
    v68$2 := (if p30$2 then $$v2z$3bv32$2 else v68$2);
    v69$1 := (if p30$1 then BV8_SEXT32(v67$1) == BV8_SEXT32(v68$1) else v69$1);
    v69$2 := (if p30$2 then BV8_SEXT32(v67$2) == BV8_SEXT32(v68$2) else v69$2);
    p31$1 := (if p30$1 && v69$1 then v69$1 else p31$1);
    p31$2 := (if p30$2 && v69$2 then v69$2 else p31$2);
    p38$1 := (if p30$1 && !v69$1 then !v69$1 else p38$1);
    p38$2 := (if p30$2 && !v69$2 then !v69$2 else p38$2);
    v70$1 := (if p31$1 then $$w$20bv32$1 else v70$1);
    v70$2 := (if p31$2 then $$w$20bv32$2 else v70$2);
    v71$1 := (if p31$1 then $$v2z$4bv32$1 else v71$1);
    v71$2 := (if p31$2 then $$v2z$4bv32$2 else v71$2);
    v72$1 := (if p31$1 then BV8_SEXT32(v70$1) == BV8_SEXT32(v71$1) else v72$1);
    v72$2 := (if p31$2 then BV8_SEXT32(v70$2) == BV8_SEXT32(v71$2) else v72$2);
    p32$1 := (if p31$1 && v72$1 then v72$1 else p32$1);
    p32$2 := (if p31$2 && v72$2 then v72$2 else p32$2);
    p37$1 := (if p31$1 && !v72$1 then !v72$1 else p37$1);
    p37$2 := (if p31$2 && !v72$2 then !v72$2 else p37$2);
    v73$1 := (if p32$1 then $$w$21bv32$1 else v73$1);
    v73$2 := (if p32$2 then $$w$21bv32$2 else v73$2);
    v74$1 := (if p32$1 then $$v2z$5bv32$1 else v74$1);
    v74$2 := (if p32$2 then $$v2z$5bv32$2 else v74$2);
    v75$1 := (if p32$1 then BV8_SEXT32(v73$1) == BV8_SEXT32(v74$1) else v75$1);
    v75$2 := (if p32$2 then BV8_SEXT32(v73$2) == BV8_SEXT32(v74$2) else v75$2);
    p33$1 := (if p32$1 && v75$1 then v75$1 else p33$1);
    p33$2 := (if p32$2 && v75$2 then v75$2 else p33$2);
    p36$1 := (if p32$1 && !v75$1 then !v75$1 else p36$1);
    p36$2 := (if p32$2 && !v75$2 then !v75$2 else p36$2);
    v76$1 := (if p33$1 then $$w$22bv32$1 else v76$1);
    v76$2 := (if p33$2 then $$w$22bv32$2 else v76$2);
    v77$1 := (if p33$1 then $$v2z$6bv32$1 else v77$1);
    v77$2 := (if p33$2 then $$v2z$6bv32$2 else v77$2);
    v78$1 := (if p33$1 then BV8_SEXT32(v76$1) == BV8_SEXT32(v77$1) else v78$1);
    v78$2 := (if p33$2 then BV8_SEXT32(v76$2) == BV8_SEXT32(v77$2) else v78$2);
    p34$1 := (if p33$1 && v78$1 then v78$1 else p34$1);
    p34$2 := (if p33$2 && v78$2 then v78$2 else p34$2);
    p35$1 := (if p33$1 && !v78$1 then !v78$1 else p35$1);
    p35$2 := (if p33$2 && !v78$2 then !v78$2 else p35$2);
    v79$1 := (if p34$1 then $$w$23bv32$1 else v79$1);
    v79$2 := (if p34$2 then $$w$23bv32$2 else v79$2);
    v80$1 := (if p34$1 then $$v2z$7bv32$1 else v80$1);
    v80$2 := (if p34$2 then $$v2z$7bv32$2 else v80$2);
    $2$1 := (if p34$1 then (if BV8_SEXT32(v79$1) == BV8_SEXT32(v80$1) then 1bv1 else 0bv1) else $2$1);
    $2$2 := (if p34$2 then (if BV8_SEXT32(v79$2) == BV8_SEXT32(v80$2) then 1bv1 else 0bv1) else $2$2);
    $2$1 := (if p35$1 then 0bv1 else $2$1);
    $2$2 := (if p35$2 then 0bv1 else $2$2);
    $2$1 := (if p36$1 then 0bv1 else $2$1);
    $2$2 := (if p36$2 then 0bv1 else $2$2);
    $2$1 := (if p37$1 then 0bv1 else $2$1);
    $2$2 := (if p37$2 then 0bv1 else $2$2);
    $2$1 := (if p38$1 then 0bv1 else $2$1);
    $2$2 := (if p38$2 then 0bv1 else $2$2);
    $2$1 := (if p39$1 then 0bv1 else $2$1);
    $2$2 := (if p39$2 then 0bv1 else $2$2);
    $2$1 := (if p40$1 then 0bv1 else $2$1);
    $2$2 := (if p40$2 then 0bv1 else $2$2);
    $2$1 := (if p41$1 then 0bv1 else $2$1);
    $2$2 := (if p41$2 then 0bv1 else $2$2);
    assert {:sourceloc_num 143} {:thread 1} $2$1 != 0bv1;
    assert {:sourceloc_num 143} {:thread 2} $2$2 != 0bv1;
    v81$1 := $$w$24bv32$1;
    v81$2 := $$w$24bv32$2;
    v82$1 := $$v2w$0bv32$1;
    v82$2 := $$v2w$0bv32$2;
    v83$1 := BV8_SEXT32(v81$1) == BV8_SEXT32(v82$1);
    v83$2 := BV8_SEXT32(v81$2) == BV8_SEXT32(v82$2);
    p42$1 := (if v83$1 then v83$1 else p42$1);
    p42$2 := (if v83$2 then v83$2 else p42$2);
    p55$1 := (if !v83$1 then !v83$1 else p55$1);
    p55$2 := (if !v83$2 then !v83$2 else p55$2);
    v84$1 := (if p42$1 then $$w$25bv32$1 else v84$1);
    v84$2 := (if p42$2 then $$w$25bv32$2 else v84$2);
    v85$1 := (if p42$1 then $$v2w$1bv32$1 else v85$1);
    v85$2 := (if p42$2 then $$v2w$1bv32$2 else v85$2);
    v86$1 := (if p42$1 then BV8_SEXT32(v84$1) == BV8_SEXT32(v85$1) else v86$1);
    v86$2 := (if p42$2 then BV8_SEXT32(v84$2) == BV8_SEXT32(v85$2) else v86$2);
    p43$1 := (if p42$1 && v86$1 then v86$1 else p43$1);
    p43$2 := (if p42$2 && v86$2 then v86$2 else p43$2);
    p54$1 := (if p42$1 && !v86$1 then !v86$1 else p54$1);
    p54$2 := (if p42$2 && !v86$2 then !v86$2 else p54$2);
    v87$1 := (if p43$1 then $$w$26bv32$1 else v87$1);
    v87$2 := (if p43$2 then $$w$26bv32$2 else v87$2);
    v88$1 := (if p43$1 then $$v2w$2bv32$1 else v88$1);
    v88$2 := (if p43$2 then $$v2w$2bv32$2 else v88$2);
    v89$1 := (if p43$1 then BV8_SEXT32(v87$1) == BV8_SEXT32(v88$1) else v89$1);
    v89$2 := (if p43$2 then BV8_SEXT32(v87$2) == BV8_SEXT32(v88$2) else v89$2);
    p44$1 := (if p43$1 && v89$1 then v89$1 else p44$1);
    p44$2 := (if p43$2 && v89$2 then v89$2 else p44$2);
    p53$1 := (if p43$1 && !v89$1 then !v89$1 else p53$1);
    p53$2 := (if p43$2 && !v89$2 then !v89$2 else p53$2);
    v90$1 := (if p44$1 then $$w$27bv32$1 else v90$1);
    v90$2 := (if p44$2 then $$w$27bv32$2 else v90$2);
    v91$1 := (if p44$1 then $$v2w$3bv32$1 else v91$1);
    v91$2 := (if p44$2 then $$v2w$3bv32$2 else v91$2);
    v92$1 := (if p44$1 then BV8_SEXT32(v90$1) == BV8_SEXT32(v91$1) else v92$1);
    v92$2 := (if p44$2 then BV8_SEXT32(v90$2) == BV8_SEXT32(v91$2) else v92$2);
    p45$1 := (if p44$1 && v92$1 then v92$1 else p45$1);
    p45$2 := (if p44$2 && v92$2 then v92$2 else p45$2);
    p52$1 := (if p44$1 && !v92$1 then !v92$1 else p52$1);
    p52$2 := (if p44$2 && !v92$2 then !v92$2 else p52$2);
    v93$1 := (if p45$1 then $$w$28bv32$1 else v93$1);
    v93$2 := (if p45$2 then $$w$28bv32$2 else v93$2);
    v94$1 := (if p45$1 then $$v2w$4bv32$1 else v94$1);
    v94$2 := (if p45$2 then $$v2w$4bv32$2 else v94$2);
    v95$1 := (if p45$1 then BV8_SEXT32(v93$1) == BV8_SEXT32(v94$1) else v95$1);
    v95$2 := (if p45$2 then BV8_SEXT32(v93$2) == BV8_SEXT32(v94$2) else v95$2);
    p46$1 := (if p45$1 && v95$1 then v95$1 else p46$1);
    p46$2 := (if p45$2 && v95$2 then v95$2 else p46$2);
    p51$1 := (if p45$1 && !v95$1 then !v95$1 else p51$1);
    p51$2 := (if p45$2 && !v95$2 then !v95$2 else p51$2);
    v96$1 := (if p46$1 then $$w$29bv32$1 else v96$1);
    v96$2 := (if p46$2 then $$w$29bv32$2 else v96$2);
    v97$1 := (if p46$1 then $$v2w$5bv32$1 else v97$1);
    v97$2 := (if p46$2 then $$v2w$5bv32$2 else v97$2);
    v98$1 := (if p46$1 then BV8_SEXT32(v96$1) == BV8_SEXT32(v97$1) else v98$1);
    v98$2 := (if p46$2 then BV8_SEXT32(v96$2) == BV8_SEXT32(v97$2) else v98$2);
    p47$1 := (if p46$1 && v98$1 then v98$1 else p47$1);
    p47$2 := (if p46$2 && v98$2 then v98$2 else p47$2);
    p50$1 := (if p46$1 && !v98$1 then !v98$1 else p50$1);
    p50$2 := (if p46$2 && !v98$2 then !v98$2 else p50$2);
    v99$1 := (if p47$1 then $$w$30bv32$1 else v99$1);
    v99$2 := (if p47$2 then $$w$30bv32$2 else v99$2);
    v100$1 := (if p47$1 then $$v2w$6bv32$1 else v100$1);
    v100$2 := (if p47$2 then $$v2w$6bv32$2 else v100$2);
    v101$1 := (if p47$1 then BV8_SEXT32(v99$1) == BV8_SEXT32(v100$1) else v101$1);
    v101$2 := (if p47$2 then BV8_SEXT32(v99$2) == BV8_SEXT32(v100$2) else v101$2);
    p48$1 := (if p47$1 && v101$1 then v101$1 else p48$1);
    p48$2 := (if p47$2 && v101$2 then v101$2 else p48$2);
    p49$1 := (if p47$1 && !v101$1 then !v101$1 else p49$1);
    p49$2 := (if p47$2 && !v101$2 then !v101$2 else p49$2);
    v102$1 := (if p48$1 then $$w$31bv32$1 else v102$1);
    v102$2 := (if p48$2 then $$w$31bv32$2 else v102$2);
    v103$1 := (if p48$1 then $$v2w$7bv32$1 else v103$1);
    v103$2 := (if p48$2 then $$v2w$7bv32$2 else v103$2);
    $3$1 := (if p48$1 then (if BV8_SEXT32(v102$1) == BV8_SEXT32(v103$1) then 1bv1 else 0bv1) else $3$1);
    $3$2 := (if p48$2 then (if BV8_SEXT32(v102$2) == BV8_SEXT32(v103$2) then 1bv1 else 0bv1) else $3$2);
    $3$1 := (if p49$1 then 0bv1 else $3$1);
    $3$2 := (if p49$2 then 0bv1 else $3$2);
    $3$1 := (if p50$1 then 0bv1 else $3$1);
    $3$2 := (if p50$2 then 0bv1 else $3$2);
    $3$1 := (if p51$1 then 0bv1 else $3$1);
    $3$2 := (if p51$2 then 0bv1 else $3$2);
    $3$1 := (if p52$1 then 0bv1 else $3$1);
    $3$2 := (if p52$2 then 0bv1 else $3$2);
    $3$1 := (if p53$1 then 0bv1 else $3$1);
    $3$2 := (if p53$2 then 0bv1 else $3$2);
    $3$1 := (if p54$1 then 0bv1 else $3$1);
    $3$2 := (if p54$2 then 0bv1 else $3$2);
    $3$1 := (if p55$1 then 0bv1 else $3$1);
    $3$2 := (if p55$2 then 0bv1 else $3$2);
    assert {:sourceloc_num 168} {:thread 1} $3$1 != 0bv1;
    assert {:sourceloc_num 168} {:thread 2} $3$2 != 0bv1;
    v104$1 := $$w$0bv32$1;
    v104$2 := $$w$0bv32$2;
    v105$1 := $$w$1bv32$1;
    v105$2 := $$w$1bv32$2;
    v106$1 := $$w$2bv32$1;
    v106$2 := $$w$2bv32$2;
    v107$1 := $$w$3bv32$1;
    v107$2 := $$w$3bv32$2;
    v108$1 := $$w$4bv32$1;
    v108$2 := $$w$4bv32$2;
    v109$1 := $$w$5bv32$1;
    v109$2 := $$w$5bv32$2;
    v110$1 := $$w$6bv32$1;
    v110$2 := $$w$6bv32$2;
    v111$1 := $$w$7bv32$1;
    v111$2 := $$w$7bv32$2;
    v112$1 := $$w$8bv32$1;
    v112$2 := $$w$8bv32$2;
    v113$1 := $$w$9bv32$1;
    v113$2 := $$w$9bv32$2;
    v114$1 := $$w$10bv32$1;
    v114$2 := $$w$10bv32$2;
    v115$1 := $$w$11bv32$1;
    v115$2 := $$w$11bv32$2;
    v116$1 := $$w$12bv32$1;
    v116$2 := $$w$12bv32$2;
    v117$1 := $$w$13bv32$1;
    v117$2 := $$w$13bv32$2;
    v118$1 := $$w$14bv32$1;
    v118$2 := $$w$14bv32$2;
    v119$1 := $$w$15bv32$1;
    v119$2 := $$w$15bv32$2;
    v120$1 := $$w$16bv32$1;
    v120$2 := $$w$16bv32$2;
    v121$1 := $$w$17bv32$1;
    v121$2 := $$w$17bv32$2;
    v122$1 := $$w$18bv32$1;
    v122$2 := $$w$18bv32$2;
    v123$1 := $$w$19bv32$1;
    v123$2 := $$w$19bv32$2;
    v124$1 := $$w$20bv32$1;
    v124$2 := $$w$20bv32$2;
    v125$1 := $$w$21bv32$1;
    v125$2 := $$w$21bv32$2;
    v126$1 := $$w$22bv32$1;
    v126$2 := $$w$22bv32$2;
    v127$1 := $$w$23bv32$1;
    v127$2 := $$w$23bv32$2;
    v128$1 := $$w$24bv32$1;
    v128$2 := $$w$24bv32$2;
    v129$1 := $$w$25bv32$1;
    v129$2 := $$w$25bv32$2;
    v130$1 := $$w$26bv32$1;
    v130$2 := $$w$26bv32$2;
    v131$1 := $$w$27bv32$1;
    v131$2 := $$w$27bv32$2;
    v132$1 := $$w$28bv32$1;
    v132$2 := $$w$28bv32$2;
    v133$1 := $$w$29bv32$1;
    v133$2 := $$w$29bv32$2;
    v134$1 := $$w$30bv32$1;
    v134$2 := $$w$30bv32$2;
    v135$1 := $$w$31bv32$1;
    v135$2 := $$w$31bv32$2;
    call _LOG_WRITE_$$p(true, BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), v111$1 ++ v110$1 ++ v109$1 ++ v108$1 ++ v107$1 ++ v106$1 ++ v105$1 ++ v104$1, $$p[BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$p(true, BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32));
    assume {:do_not_predicate} {:check_id "check_state_4"} {:captureState "check_state_4"} {:sourceloc} {:sourceloc_num 201} true;
    call _CHECK_WRITE_$$p(true, BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), v111$2 ++ v110$2 ++ v109$2 ++ v108$2 ++ v107$2 ++ v106$2 ++ v105$2 ++ v104$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$p"} true;
    $$p[BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32)] := v111$1 ++ v110$1 ++ v109$1 ++ v108$1 ++ v107$1 ++ v106$1 ++ v105$1 ++ v104$1;
    $$p[BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32)] := v111$2 ++ v110$2 ++ v109$2 ++ v108$2 ++ v107$2 ++ v106$2 ++ v105$2 ++ v104$2;
    call _LOG_WRITE_$$p(true, BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 1bv32), v119$1 ++ v118$1 ++ v117$1 ++ v116$1 ++ v115$1 ++ v114$1 ++ v113$1 ++ v112$1, $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$p(true, BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_5"} {:captureState "check_state_5"} {:sourceloc} {:sourceloc_num 202} true;
    call _CHECK_WRITE_$$p(true, BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 1bv32), v119$2 ++ v118$2 ++ v117$2 ++ v116$2 ++ v115$2 ++ v114$2 ++ v113$2 ++ v112$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$p"} true;
    $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 1bv32)] := v119$1 ++ v118$1 ++ v117$1 ++ v116$1 ++ v115$1 ++ v114$1 ++ v113$1 ++ v112$1;
    $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 1bv32)] := v119$2 ++ v118$2 ++ v117$2 ++ v116$2 ++ v115$2 ++ v114$2 ++ v113$2 ++ v112$2;
    call _LOG_WRITE_$$p(true, BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 2bv32), v127$1 ++ v126$1 ++ v125$1 ++ v124$1 ++ v123$1 ++ v122$1 ++ v121$1 ++ v120$1, $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 2bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$p(true, BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 2bv32));
    assume {:do_not_predicate} {:check_id "check_state_6"} {:captureState "check_state_6"} {:sourceloc} {:sourceloc_num 203} true;
    call _CHECK_WRITE_$$p(true, BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 2bv32), v127$2 ++ v126$2 ++ v125$2 ++ v124$2 ++ v123$2 ++ v122$2 ++ v121$2 ++ v120$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$p"} true;
    $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 2bv32)] := v127$1 ++ v126$1 ++ v125$1 ++ v124$1 ++ v123$1 ++ v122$1 ++ v121$1 ++ v120$1;
    $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 2bv32)] := v127$2 ++ v126$2 ++ v125$2 ++ v124$2 ++ v123$2 ++ v122$2 ++ v121$2 ++ v120$2;
    call _LOG_WRITE_$$p(true, BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 3bv32), v135$1 ++ v134$1 ++ v133$1 ++ v132$1 ++ v131$1 ++ v130$1 ++ v129$1 ++ v128$1, $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 3bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$p(true, BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 3bv32));
    assume {:do_not_predicate} {:check_id "check_state_7"} {:captureState "check_state_7"} {:sourceloc} {:sourceloc_num 204} true;
    call _CHECK_WRITE_$$p(true, BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 3bv32), v135$2 ++ v134$2 ++ v133$2 ++ v132$2 ++ v131$2 ++ v130$2 ++ v129$2 ++ v128$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$p"} true;
    $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 4bv32), 3bv32)] := v135$1 ++ v134$1 ++ v133$1 ++ v132$1 ++ v131$1 ++ v130$1 ++ v129$1 ++ v128$1;
    $$p[BV32_ADD(BV32_MUL(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 4bv32), 3bv32)] := v135$2 ++ v134$2 ++ v133$2 ++ v132$2 ++ v131$2 ++ v130$2 ++ v129$2 ++ v128$2;
    return;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 2048bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 1111bv32 then 1bv1 else 0bv1) != 0bv1;

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

var $$w$0bv32$1: bv8;

var $$w$0bv32$2: bv8;

var $$w$1bv32$1: bv8;

var $$w$1bv32$2: bv8;

var $$w$2bv32$1: bv8;

var $$w$2bv32$2: bv8;

var $$w$3bv32$1: bv8;

var $$w$3bv32$2: bv8;

var $$w$4bv32$1: bv8;

var $$w$4bv32$2: bv8;

var $$w$5bv32$1: bv8;

var $$w$5bv32$2: bv8;

var $$w$6bv32$1: bv8;

var $$w$6bv32$2: bv8;

var $$w$7bv32$1: bv8;

var $$w$7bv32$2: bv8;

var $$w$8bv32$1: bv8;

var $$w$8bv32$2: bv8;

var $$w$9bv32$1: bv8;

var $$w$9bv32$2: bv8;

var $$w$10bv32$1: bv8;

var $$w$10bv32$2: bv8;

var $$w$11bv32$1: bv8;

var $$w$11bv32$2: bv8;

var $$w$12bv32$1: bv8;

var $$w$12bv32$2: bv8;

var $$w$13bv32$1: bv8;

var $$w$13bv32$2: bv8;

var $$w$14bv32$1: bv8;

var $$w$14bv32$2: bv8;

var $$w$15bv32$1: bv8;

var $$w$15bv32$2: bv8;

var $$w$16bv32$1: bv8;

var $$w$16bv32$2: bv8;

var $$w$17bv32$1: bv8;

var $$w$17bv32$2: bv8;

var $$w$18bv32$1: bv8;

var $$w$18bv32$2: bv8;

var $$w$19bv32$1: bv8;

var $$w$19bv32$2: bv8;

var $$w$20bv32$1: bv8;

var $$w$20bv32$2: bv8;

var $$w$21bv32$1: bv8;

var $$w$21bv32$2: bv8;

var $$w$22bv32$1: bv8;

var $$w$22bv32$2: bv8;

var $$w$23bv32$1: bv8;

var $$w$23bv32$2: bv8;

var $$w$24bv32$1: bv8;

var $$w$24bv32$2: bv8;

var $$w$25bv32$1: bv8;

var $$w$25bv32$2: bv8;

var $$w$26bv32$1: bv8;

var $$w$26bv32$2: bv8;

var $$w$27bv32$1: bv8;

var $$w$27bv32$2: bv8;

var $$w$28bv32$1: bv8;

var $$w$28bv32$2: bv8;

var $$w$29bv32$1: bv8;

var $$w$29bv32$2: bv8;

var $$w$30bv32$1: bv8;

var $$w$30bv32$2: bv8;

var $$w$31bv32$1: bv8;

var $$w$31bv32$2: bv8;

var $$v2x$0bv32$1: bv8;

var $$v2x$0bv32$2: bv8;

var $$v2x$1bv32$1: bv8;

var $$v2x$1bv32$2: bv8;

var $$v2x$2bv32$1: bv8;

var $$v2x$2bv32$2: bv8;

var $$v2x$3bv32$1: bv8;

var $$v2x$3bv32$2: bv8;

var $$v2x$4bv32$1: bv8;

var $$v2x$4bv32$2: bv8;

var $$v2x$5bv32$1: bv8;

var $$v2x$5bv32$2: bv8;

var $$v2x$6bv32$1: bv8;

var $$v2x$6bv32$2: bv8;

var $$v2x$7bv32$1: bv8;

var $$v2x$7bv32$2: bv8;

var $$v2y$0bv32$1: bv8;

var $$v2y$0bv32$2: bv8;

var $$v2y$1bv32$1: bv8;

var $$v2y$1bv32$2: bv8;

var $$v2y$2bv32$1: bv8;

var $$v2y$2bv32$2: bv8;

var $$v2y$3bv32$1: bv8;

var $$v2y$3bv32$2: bv8;

var $$v2y$4bv32$1: bv8;

var $$v2y$4bv32$2: bv8;

var $$v2y$5bv32$1: bv8;

var $$v2y$5bv32$2: bv8;

var $$v2y$6bv32$1: bv8;

var $$v2y$6bv32$2: bv8;

var $$v2y$7bv32$1: bv8;

var $$v2y$7bv32$2: bv8;

var $$v2z$0bv32$1: bv8;

var $$v2z$0bv32$2: bv8;

var $$v2z$1bv32$1: bv8;

var $$v2z$1bv32$2: bv8;

var $$v2z$2bv32$1: bv8;

var $$v2z$2bv32$2: bv8;

var $$v2z$3bv32$1: bv8;

var $$v2z$3bv32$2: bv8;

var $$v2z$4bv32$1: bv8;

var $$v2z$4bv32$2: bv8;

var $$v2z$5bv32$1: bv8;

var $$v2z$5bv32$2: bv8;

var $$v2z$6bv32$1: bv8;

var $$v2z$6bv32$2: bv8;

var $$v2z$7bv32$1: bv8;

var $$v2z$7bv32$2: bv8;

var $$v2w$0bv32$1: bv8;

var $$v2w$0bv32$2: bv8;

var $$v2w$1bv32$1: bv8;

var $$v2w$1bv32$2: bv8;

var $$v2w$2bv32$1: bv8;

var $$v2w$2bv32$2: bv8;

var $$v2w$3bv32$1: bv8;

var $$v2w$3bv32$2: bv8;

var $$v2w$4bv32$1: bv8;

var $$v2w$4bv32$2: bv8;

var $$v2w$5bv32$1: bv8;

var $$v2w$5bv32$2: bv8;

var $$v2w$6bv32$1: bv8;

var $$v2w$6bv32$2: bv8;

var $$v2w$7bv32$1: bv8;

var $$v2w$7bv32$2: bv8;

const _WATCHED_VALUE_$$p: bv64;

procedure {:inline 1} _LOG_READ_$$p(_P: bool, _offset: bv32, _value: bv64);
  modifies _READ_HAS_OCCURRED_$$p;

implementation {:inline 1} _LOG_READ_$$p(_P: bool, _offset: bv32, _value: bv64)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then true else _READ_HAS_OCCURRED_$$p);
    return;
}

procedure _CHECK_READ_$$p(_P: bool, _offset: bv32, _value: bv64);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$p);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$p: bool;

procedure {:inline 1} _LOG_WRITE_$$p(_P: bool, _offset: bv32, _value: bv64, _value_old: bv64);
  modifies _WRITE_HAS_OCCURRED_$$p, _WRITE_READ_BENIGN_FLAG_$$p;

implementation {:inline 1} _LOG_WRITE_$$p(_P: bool, _offset: bv32, _value: bv64, _value_old: bv64)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then true else _WRITE_HAS_OCCURRED_$$p);
    _WRITE_READ_BENIGN_FLAG_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$p);
    return;
}

procedure _CHECK_WRITE_$$p(_P: bool, _offset: bv32, _value: bv64);
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
