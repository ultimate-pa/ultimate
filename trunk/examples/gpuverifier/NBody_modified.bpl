type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);



axiom {:array_info "$$pos"} {:global} {:elem_width 32} {:source_name "pos"} {:source_elem_width 128} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$pos: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$pos: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$pos: bool;

axiom {:array_info "$$vel"} {:global} {:elem_width 32} {:source_name "vel"} {:source_elem_width 128} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$vel: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$vel: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$vel: bool;

var {:source_name "localPos"} {:group_shared} $$localPos: [bv1][bv32]bv32;

axiom {:array_info "$$localPos"} {:group_shared} {:elem_width 32} {:source_name "localPos"} {:source_elem_width 128} {:source_dimensions "*"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$localPos: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$localPos: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$localPos: bool;

var {:source_name "newPosition"} {:global} $$newPosition: [bv32]bv32;

axiom {:array_info "$$newPosition"} {:global} {:elem_width 32} {:source_name "newPosition"} {:source_elem_width 128} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$newPosition: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$newPosition: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$newPosition: bool;

var {:source_name "newVelocity"} {:global} $$newVelocity: [bv32]bv32;

axiom {:array_info "$$newVelocity"} {:global} {:elem_width 32} {:source_name "newVelocity"} {:source_elem_width 128} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$newVelocity: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$newVelocity: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$newVelocity: bool;

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

function FADD32(bv32, bv32) : bv32;

function FDIV32(bv32, bv32) : bv32;

function FMUL32(bv32, bv32) : bv32;

function FSQRT32(bv32) : bv32;

function FSUB32(bv32, bv32) : bv32;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

function {:builtin "bvudiv"} BV32_UDIV(bv32, bv32) : bv32;

function {:builtin "bvult"} BV32_ULT(bv32, bv32) : bool;

procedure {:source_name "nbody_sim"} {:kernel} ULTIMATE.start($numBodies: bv32, $deltaTime: bv32, $epsSqr: bv32);
  requires !_READ_HAS_OCCURRED_$$pos && !_WRITE_HAS_OCCURRED_$$pos && !_ATOMIC_HAS_OCCURRED_$$pos;
  requires !_READ_HAS_OCCURRED_$$vel && !_WRITE_HAS_OCCURRED_$$vel && !_ATOMIC_HAS_OCCURRED_$$vel;
  requires !_READ_HAS_OCCURRED_$$newPosition && !_WRITE_HAS_OCCURRED_$$newPosition && !_ATOMIC_HAS_OCCURRED_$$newPosition;
  requires !_READ_HAS_OCCURRED_$$newVelocity && !_WRITE_HAS_OCCURRED_$$newVelocity && !_ATOMIC_HAS_OCCURRED_$$newVelocity;
  requires !_READ_HAS_OCCURRED_$$localPos && !_WRITE_HAS_OCCURRED_$$localPos && !_ATOMIC_HAS_OCCURRED_$$localPos;
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
  modifies $$localPos, _WRITE_HAS_OCCURRED_$$newPosition, _WRITE_READ_BENIGN_FLAG_$$newPosition, _WRITE_READ_BENIGN_FLAG_$$newPosition, _WRITE_HAS_OCCURRED_$$newVelocity, _WRITE_READ_BENIGN_FLAG_$$newVelocity, _WRITE_READ_BENIGN_FLAG_$$newVelocity, _WRITE_HAS_OCCURRED_$$localPos, _WRITE_READ_BENIGN_FLAG_$$localPos, _WRITE_READ_BENIGN_FLAG_$$localPos, $$newPosition, $$newVelocity, _TRACKING, _TRACKING, _READ_HAS_OCCURRED_$$localPos;



implementation {:source_name "nbody_sim"} {:kernel} ULTIMATE.start($numBodies: bv32, $deltaTime: bv32, $epsSqr: bv32)
{
  var $acc.0$1: bv128;
  var $acc.0$2: bv128;
  var $i.0: bv32;
  var $acc.1$1: bv128;
  var $acc.1$2: bv128;
  var $j.0: bv32;
  var v0$1: bv32;
  var v0$2: bv32;
  var v1$1: bv32;
  var v1$2: bv32;
  var v2: bv32;
  var v3$1: bv32;
  var v3$2: bv32;
  var v4$1: bv32;
  var v4$2: bv32;
  var v5$1: bv32;
  var v5$2: bv32;
  var v6$1: bv32;
  var v6$2: bv32;
  var v7: bool;
  var v8$1: bv32;
  var v8$2: bv32;
  var v9$1: bv32;
  var v9$2: bv32;
  var v10$1: bv32;
  var v10$2: bv32;
  var v11$1: bv32;
  var v11$2: bv32;
  var v12: bool;
  var v13$1: bv32;
  var v13$2: bv32;
  var v14$1: bv32;
  var v14$2: bv32;
  var v15$1: bv32;
  var v15$2: bv32;
  var v19$1: bv32;
  var v19$2: bv32;
  var v16$1: bv32;
  var v16$2: bv32;
  var v17$1: bv32;
  var v17$2: bv32;
  var v18$1: bv32;
  var v18$2: bv32;
  var v20$1: bv32;
  var v20$2: bv32;
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


  $entry:
    v0$1 := local_id_x$1;
    v0$2 := local_id_x$2;
    v1$1 := BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1);
    v1$2 := BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2);
    v2 := group_size_x;
    havoc v3$1, v3$2;
    havoc v4$1, v4$2;
    havoc v5$1, v5$2;
    havoc v6$1, v6$2;
    $acc.0$1, $i.0 := 0bv128, 0bv32;
    $acc.0$2 := 0bv128;
    assume {:captureState "loop_entry_state_0_0"} true;
    goto $for.cond;

  $for.cond:
    assume {:captureState "loop_head_state_0"} true;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _ATOMIC_HAS_OCCURRED_$$localPos ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _WRITE_HAS_OCCURRED_$$localPos ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _READ_HAS_OCCURRED_$$localPos ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:block_sourceloc} {:sourceloc_num 5} true;
    v7 := BV32_ULT($i.0, BV32_UDIV($numBodies, v2));
    goto __partitioned_block_$truebb_0, $falsebb;

  $falsebb:
    assume {:partition} !v7;
    havoc v26$1, v26$2;
    havoc v27$1, v27$2;
    havoc v28$1, v28$2;
    havoc v29$1, v29$2;
    call _LOG_WRITE_$$newPosition(true, BV32_MUL(v1$1, 4bv32), FADD32(FMUL32(FMUL32(FMUL32($acc.0$1[32:0], 1056964608bv32), $deltaTime), $deltaTime), FADD32(FMUL32(v26$1, $deltaTime), v3$1)), $$newPosition[BV32_MUL(v1$1, 4bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$newPosition(true, BV32_MUL(v1$2, 4bv32));
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 35} true;
    call _CHECK_WRITE_$$newPosition(true, BV32_MUL(v1$2, 4bv32), FADD32(FMUL32(FMUL32(FMUL32($acc.0$2[32:0], 1056964608bv32), $deltaTime), $deltaTime), FADD32(FMUL32(v26$2, $deltaTime), v3$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$newPosition"} true;
    $$newPosition[BV32_MUL(v1$1, 4bv32)] := FADD32(FMUL32(FMUL32(FMUL32($acc.0$1[32:0], 1056964608bv32), $deltaTime), $deltaTime), FADD32(FMUL32(v26$1, $deltaTime), v3$1));
    $$newPosition[BV32_MUL(v1$2, 4bv32)] := FADD32(FMUL32(FMUL32(FMUL32($acc.0$2[32:0], 1056964608bv32), $deltaTime), $deltaTime), FADD32(FMUL32(v26$2, $deltaTime), v3$2));
    call _LOG_WRITE_$$newPosition(true, BV32_ADD(BV32_MUL(v1$1, 4bv32), 1bv32), FADD32(FMUL32(FMUL32(FMUL32($acc.0$1[64:32], 1056964608bv32), $deltaTime), $deltaTime), FADD32(FMUL32(v27$1, $deltaTime), v4$1)), $$newPosition[BV32_ADD(BV32_MUL(v1$1, 4bv32), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$newPosition(true, BV32_ADD(BV32_MUL(v1$2, 4bv32), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 36} true;
    call _CHECK_WRITE_$$newPosition(true, BV32_ADD(BV32_MUL(v1$2, 4bv32), 1bv32), FADD32(FMUL32(FMUL32(FMUL32($acc.0$2[64:32], 1056964608bv32), $deltaTime), $deltaTime), FADD32(FMUL32(v27$2, $deltaTime), v4$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$newPosition"} true;
    $$newPosition[BV32_ADD(BV32_MUL(v1$1, 4bv32), 1bv32)] := FADD32(FMUL32(FMUL32(FMUL32($acc.0$1[64:32], 1056964608bv32), $deltaTime), $deltaTime), FADD32(FMUL32(v27$1, $deltaTime), v4$1));
    $$newPosition[BV32_ADD(BV32_MUL(v1$2, 4bv32), 1bv32)] := FADD32(FMUL32(FMUL32(FMUL32($acc.0$2[64:32], 1056964608bv32), $deltaTime), $deltaTime), FADD32(FMUL32(v27$2, $deltaTime), v4$2));
    call _LOG_WRITE_$$newPosition(true, BV32_ADD(BV32_MUL(v1$1, 4bv32), 2bv32), FADD32(FMUL32(FMUL32(FMUL32($acc.0$1[96:64], 1056964608bv32), $deltaTime), $deltaTime), FADD32(FMUL32(v28$1, $deltaTime), v5$1)), $$newPosition[BV32_ADD(BV32_MUL(v1$1, 4bv32), 2bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$newPosition(true, BV32_ADD(BV32_MUL(v1$2, 4bv32), 2bv32));
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 37} true;
    call  _CHECK_WRITE_$$newPosition(true, BV32_ADD(BV32_MUL(v1$2, 4bv32), 2bv32), FADD32(FMUL32(FMUL32(FMUL32($acc.0$2[96:64], 1056964608bv32), $deltaTime), $deltaTime), FADD32(FMUL32(v28$2, $deltaTime), v5$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$newPosition"} true;
    $$newPosition[BV32_ADD(BV32_MUL(v1$1, 4bv32), 2bv32)] := FADD32(FMUL32(FMUL32(FMUL32($acc.0$1[96:64], 1056964608bv32), $deltaTime), $deltaTime), FADD32(FMUL32(v28$1, $deltaTime), v5$1));
    $$newPosition[BV32_ADD(BV32_MUL(v1$2, 4bv32), 2bv32)] := FADD32(FMUL32(FMUL32(FMUL32($acc.0$2[96:64], 1056964608bv32), $deltaTime), $deltaTime), FADD32(FMUL32(v28$2, $deltaTime), v5$2));
    call  _LOG_WRITE_$$newPosition(true, BV32_ADD(BV32_MUL(v1$1, 4bv32), 3bv32), v6$1, $$newPosition[BV32_ADD(BV32_MUL(v1$1, 4bv32), 3bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$newPosition(true, BV32_ADD(BV32_MUL(v1$2, 4bv32), 3bv32));
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 38} true;
    call  _CHECK_WRITE_$$newPosition(true, BV32_ADD(BV32_MUL(v1$2, 4bv32), 3bv32), v6$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$newPosition"} true;
    $$newPosition[BV32_ADD(BV32_MUL(v1$1, 4bv32), 3bv32)] := v6$1;
    $$newPosition[BV32_ADD(BV32_MUL(v1$2, 4bv32), 3bv32)] := v6$2;
    call  _LOG_WRITE_$$newVelocity(true, BV32_MUL(v1$1, 4bv32), FADD32(FMUL32($acc.0$1[32:0], $deltaTime), v26$1), $$newVelocity[BV32_MUL(v1$1, 4bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$newVelocity(true, BV32_MUL(v1$2, 4bv32));
    assume {:do_not_predicate} {:check_id "check_state_4"} {:captureState "check_state_4"} {:sourceloc} {:sourceloc_num 39} true;
    call  _CHECK_WRITE_$$newVelocity(true, BV32_MUL(v1$2, 4bv32), FADD32(FMUL32($acc.0$2[32:0], $deltaTime), v26$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$newVelocity"} true;
    $$newVelocity[BV32_MUL(v1$1, 4bv32)] := FADD32(FMUL32($acc.0$1[32:0], $deltaTime), v26$1);
    $$newVelocity[BV32_MUL(v1$2, 4bv32)] := FADD32(FMUL32($acc.0$2[32:0], $deltaTime), v26$2);
    call  _LOG_WRITE_$$newVelocity(true, BV32_ADD(BV32_MUL(v1$1, 4bv32), 1bv32), FADD32(FMUL32($acc.0$1[64:32], $deltaTime), v27$1), $$newVelocity[BV32_ADD(BV32_MUL(v1$1, 4bv32), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$newVelocity(true, BV32_ADD(BV32_MUL(v1$2, 4bv32), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_5"} {:captureState "check_state_5"} {:sourceloc} {:sourceloc_num 40} true;
    call  _CHECK_WRITE_$$newVelocity(true, BV32_ADD(BV32_MUL(v1$2, 4bv32), 1bv32), FADD32(FMUL32($acc.0$2[64:32], $deltaTime), v27$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$newVelocity"} true;
    $$newVelocity[BV32_ADD(BV32_MUL(v1$1, 4bv32), 1bv32)] := FADD32(FMUL32($acc.0$1[64:32], $deltaTime), v27$1);
    $$newVelocity[BV32_ADD(BV32_MUL(v1$2, 4bv32), 1bv32)] := FADD32(FMUL32($acc.0$2[64:32], $deltaTime), v27$2);
    call  _LOG_WRITE_$$newVelocity(true, BV32_ADD(BV32_MUL(v1$1, 4bv32), 2bv32), FADD32(FMUL32($acc.0$1[96:64], $deltaTime), v28$1), $$newVelocity[BV32_ADD(BV32_MUL(v1$1, 4bv32), 2bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$newVelocity(true, BV32_ADD(BV32_MUL(v1$2, 4bv32), 2bv32));
    assume {:do_not_predicate} {:check_id "check_state_6"} {:captureState "check_state_6"} {:sourceloc} {:sourceloc_num 41} true;
    call  _CHECK_WRITE_$$newVelocity(true, BV32_ADD(BV32_MUL(v1$2, 4bv32), 2bv32), FADD32(FMUL32($acc.0$2[96:64], $deltaTime), v28$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$newVelocity"} true;
    $$newVelocity[BV32_ADD(BV32_MUL(v1$1, 4bv32), 2bv32)] := FADD32(FMUL32($acc.0$1[96:64], $deltaTime), v28$1);
    $$newVelocity[BV32_ADD(BV32_MUL(v1$2, 4bv32), 2bv32)] := FADD32(FMUL32($acc.0$2[96:64], $deltaTime), v28$2);
    call  _LOG_WRITE_$$newVelocity(true, BV32_ADD(BV32_MUL(v1$1, 4bv32), 3bv32), FADD32(FMUL32($acc.0$1[128:96], $deltaTime), v29$1), $$newVelocity[BV32_ADD(BV32_MUL(v1$1, 4bv32), 3bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$newVelocity(true, BV32_ADD(BV32_MUL(v1$2, 4bv32), 3bv32));
    assume {:do_not_predicate} {:check_id "check_state_7"} {:captureState "check_state_7"} {:sourceloc} {:sourceloc_num 42} true;
    call  _CHECK_WRITE_$$newVelocity(true, BV32_ADD(BV32_MUL(v1$2, 4bv32), 3bv32), FADD32(FMUL32($acc.0$2[128:96], $deltaTime), v29$2));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$newVelocity"} true;
    $$newVelocity[BV32_ADD(BV32_MUL(v1$1, 4bv32), 3bv32)] := FADD32(FMUL32($acc.0$1[128:96], $deltaTime), v29$1);
    $$newVelocity[BV32_ADD(BV32_MUL(v1$2, 4bv32), 3bv32)] := FADD32(FMUL32($acc.0$2[128:96], $deltaTime), v29$2);
    return;

  __partitioned_block_$truebb_0:
    assume {:partition} v7;
    havoc v8$1, v8$2;
    havoc v9$1, v9$2;
    havoc v10$1, v10$2;
    havoc v11$1, v11$2;
    call  _LOG_WRITE_$$localPos(true, BV32_MUL(v0$1, 4bv32), v8$1, $$localPos[1bv1][BV32_MUL(v0$1, 4bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$localPos(true, BV32_MUL(v0$2, 4bv32));
    assume {:do_not_predicate} {:check_id "check_state_8"} {:captureState "check_state_8"} {:sourceloc} {:sourceloc_num 11} true;
    call  _CHECK_WRITE_$$localPos(true, BV32_MUL(v0$2, 4bv32), v8$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$localPos"} true;
    $$localPos[1bv1][BV32_MUL(v0$1, 4bv32)] := v8$1;
    $$localPos[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_MUL(v0$2, 4bv32)] := v8$2;
    call  _LOG_WRITE_$$localPos(true, BV32_ADD(BV32_MUL(v0$1, 4bv32), 1bv32), v9$1, $$localPos[1bv1][BV32_ADD(BV32_MUL(v0$1, 4bv32), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$localPos(true, BV32_ADD(BV32_MUL(v0$2, 4bv32), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_9"} {:captureState "check_state_9"} {:sourceloc} {:sourceloc_num 12} true;
    call  _CHECK_WRITE_$$localPos(true, BV32_ADD(BV32_MUL(v0$2, 4bv32), 1bv32), v9$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$localPos"} true;
    $$localPos[1bv1][BV32_ADD(BV32_MUL(v0$1, 4bv32), 1bv32)] := v9$1;
    $$localPos[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(v0$2, 4bv32), 1bv32)] := v9$2;
    call  _LOG_WRITE_$$localPos(true, BV32_ADD(BV32_MUL(v0$1, 4bv32), 2bv32), v10$1, $$localPos[1bv1][BV32_ADD(BV32_MUL(v0$1, 4bv32), 2bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$localPos(true, BV32_ADD(BV32_MUL(v0$2, 4bv32), 2bv32));
    assume {:do_not_predicate} {:check_id "check_state_10"} {:captureState "check_state_10"} {:sourceloc} {:sourceloc_num 13} true;
    call  _CHECK_WRITE_$$localPos(true, BV32_ADD(BV32_MUL(v0$2, 4bv32), 2bv32), v10$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$localPos"} true;
    $$localPos[1bv1][BV32_ADD(BV32_MUL(v0$1, 4bv32), 2bv32)] := v10$1;
    $$localPos[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(v0$2, 4bv32), 2bv32)] := v10$2;
    call  _LOG_WRITE_$$localPos(true, BV32_ADD(BV32_MUL(v0$1, 4bv32), 3bv32), v11$1, $$localPos[1bv1][BV32_ADD(BV32_MUL(v0$1, 4bv32), 3bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$localPos(true, BV32_ADD(BV32_MUL(v0$2, 4bv32), 3bv32));
    assume {:do_not_predicate} {:check_id "check_state_11"} {:captureState "check_state_11"} {:sourceloc} {:sourceloc_num 14} true;
    call  _CHECK_WRITE_$$localPos(true, BV32_ADD(BV32_MUL(v0$2, 4bv32), 3bv32), v11$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$localPos"} true;
    $$localPos[1bv1][BV32_ADD(BV32_MUL(v0$1, 4bv32), 3bv32)] := v11$1;
    $$localPos[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(v0$2, 4bv32), 3bv32)] := v11$2;
    goto __partitioned_block_$truebb_1;

  __partitioned_block_$truebb_1:
    call  $bugle_barrier_duplicated_0(1bv1, 0bv1);
    $acc.1$1, $j.0 := $acc.0$1, 0bv32;
    $acc.1$2 := $acc.0$2;
    assume {:captureState "loop_entry_state_1_0"} true;
    goto $for.cond5;

  $for.cond5:
    assume {:captureState "loop_head_state_1"} true;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _ATOMIC_HAS_OCCURRED_$$localPos ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _WRITE_HAS_OCCURRED_$$localPos ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _READ_HAS_OCCURRED_$$localPos ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:block_sourceloc} {:sourceloc_num 16} true;
    v12 := BV32_ULT($j.0, v2);
    goto $truebb0, __partitioned_block_$falsebb0_0;

  __partitioned_block_$falsebb0_0:
    assume {:partition} !v12;
    goto __partitioned_block_$falsebb0_1;

  __partitioned_block_$falsebb0_1:
    call  $bugle_barrier_duplicated_1(1bv1, 0bv1);
    $acc.0$1, $i.0 := $acc.1$1, BV32_ADD($i.0, 1bv32);
    $acc.0$2 := $acc.1$2;
    assume {:captureState "loop_back_edge_state_0_0"} true;
    goto $for.cond;

  $truebb0:
    assume {:partition} v12;
    assume {:do_not_predicate} {:check_id "check_state_12"} {:captureState "check_state_12"} {:sourceloc} {:sourceloc_num 18} true;
    v13$1 := $$localPos[1bv1][BV32_MUL($j.0, 4bv32)];
    v13$2 := $$localPos[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_MUL($j.0, 4bv32)];
    assume {:do_not_predicate} {:check_id "check_state_13"} {:captureState "check_state_13"} {:sourceloc} {:sourceloc_num 19} true;
    v14$1 := $$localPos[1bv1][BV32_ADD(BV32_MUL($j.0, 4bv32), 1bv32)];
    v14$2 := $$localPos[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL($j.0, 4bv32), 1bv32)];
    assume {:do_not_predicate} {:check_id "check_state_14"} {:captureState "check_state_14"} {:sourceloc} {:sourceloc_num 20} true;
    v15$1 := $$localPos[1bv1][BV32_ADD(BV32_MUL($j.0, 4bv32), 2bv32)];
    v15$2 := $$localPos[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL($j.0, 4bv32), 2bv32)];
    assume {:do_not_predicate} {:check_id "check_state_15"} {:captureState "check_state_15"} {:sourceloc} {:sourceloc_num 21} true;
    v16$1 := $$localPos[1bv1][BV32_ADD(BV32_MUL($j.0, 4bv32), 3bv32)];
    v16$2 := $$localPos[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL($j.0, 4bv32), 3bv32)];
    v17$1 := FSUB32(v13$1, v3$1);
    v17$2 := FSUB32(v13$2, v3$2);
    v18$1 := FSUB32(v14$1, v4$1);
    v18$2 := FSUB32(v14$2, v4$2);
    v19$1 := FSUB32(v15$1, v5$1);
    v19$2 := FSUB32(v15$2, v5$2);
    v20$1 := FDIV32(1065353216bv32, FSQRT32(FADD32(FADD32(FMUL32(v19$1, v19$1), FADD32(FMUL32(v17$1, v17$1), FMUL32(v18$1, v18$1))), $epsSqr)));
    v20$2 := FDIV32(1065353216bv32, FSQRT32(FADD32(FADD32(FMUL32(v19$2, v19$2), FADD32(FMUL32(v17$2, v17$2), FMUL32(v18$2, v18$2))), $epsSqr)));
    assume {:do_not_predicate} {:check_id "check_state_16"} {:captureState "check_state_16"} {:sourceloc} {:sourceloc_num 22} true;
    v21$1 := $$localPos[1bv1][BV32_MUL($j.0, 4bv32)];
    v21$2 := $$localPos[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_MUL($j.0, 4bv32)];
    assume {:do_not_predicate} {:check_id "check_state_17"} {:captureState "check_state_17"} {:sourceloc} {:sourceloc_num 23} true;
    v22$1 := $$localPos[1bv1][BV32_ADD(BV32_MUL($j.0, 4bv32), 1bv32)];
    v22$2 := $$localPos[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL($j.0, 4bv32), 1bv32)];
    assume {:do_not_predicate} {:check_id "check_state_18"} {:captureState "check_state_18"} {:sourceloc} {:sourceloc_num 24} true;
    v23$1 := $$localPos[1bv1][BV32_ADD(BV32_MUL($j.0, 4bv32), 2bv32)];
    v23$2 := $$localPos[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL($j.0, 4bv32), 2bv32)];
    assume {:do_not_predicate} {:check_id "check_state_19"} {:captureState "check_state_19"} {:sourceloc} {:sourceloc_num 25} true;
    v24$1 := $$localPos[1bv1][BV32_ADD(BV32_MUL($j.0, 4bv32), 3bv32)];
    v24$2 := $$localPos[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL($j.0, 4bv32), 3bv32)];
    v25$1 := FMUL32(v24$1, FMUL32(FMUL32(v20$1, v20$1), v20$1));
    v25$2 := FMUL32(v24$2, FMUL32(FMUL32(v20$2, v20$2), v20$2));
    $acc.1$1, $j.0 := FADD32(FMUL32(v25$1, FSUB32(v16$1, v6$1)), $acc.1$1[128:96]) ++ FADD32(FMUL32(v25$1, v19$1), $acc.1$1[96:64]) ++ FADD32(FMUL32(v25$1, v18$1), $acc.1$1[64:32]) ++ FADD32(FMUL32(v25$1, v17$1), $acc.1$1[32:0]), BV32_ADD($j.0, 1bv32);
    $acc.1$2 := FADD32(FMUL32(v25$2, FSUB32(v16$2, v6$2)), $acc.1$2[128:96]) ++ FADD32(FMUL32(v25$2, v19$2), $acc.1$2[96:64]) ++ FADD32(FMUL32(v25$2, v18$2), $acc.1$2[64:32]) ++ FADD32(FMUL32(v25$2, v17$2), $acc.1$2[32:0]);
    assume {:captureState "loop_back_edge_state_1_0"} true;
    goto $for.cond5;
}



axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 256bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 4bv32 then 1bv1 else 0bv1) != 0bv1;

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

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_0($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 0bv1;
  modifies $$localPos, $$newPosition, $$newVelocity, _TRACKING;



procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_1($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 0bv1;
  modifies $$localPos, $$newPosition, $$newVelocity, _TRACKING;



const _WATCHED_VALUE_$$pos: bv32;

procedure {:inline 1} _LOG_READ_$$pos(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$pos;



implementation {:inline 1} _LOG_READ_$$pos(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$pos := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$pos == _value then true else _READ_HAS_OCCURRED_$$pos);
    return;
}



procedure _CHECK_READ_$$pos(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$pos && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$pos);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$pos && _WATCHED_OFFSET == _offset);



var _WRITE_READ_BENIGN_FLAG_$$pos: bool;

procedure {:inline 1} _LOG_WRITE_$$pos(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$pos, _WRITE_READ_BENIGN_FLAG_$$pos;



implementation {:inline 1} _LOG_WRITE_$$pos(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$pos := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$pos == _value then true else _WRITE_HAS_OCCURRED_$$pos);
    _WRITE_READ_BENIGN_FLAG_$$pos := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$pos == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$pos);
    return;
}



procedure _CHECK_WRITE_$$pos(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$pos && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$pos != _value);
  requires  !(_P && _READ_HAS_OCCURRED_$$pos && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$pos != _value);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$pos && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _LOG_ATOMIC_$$pos(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$pos;



implementation {:inline 1} _LOG_ATOMIC_$$pos(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$pos := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$pos);
    return;
}



procedure _CHECK_ATOMIC_$$pos(_P: bool, _offset: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$pos && _WATCHED_OFFSET == _offset);
  requires  !(_P && _READ_HAS_OCCURRED_$$pos && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$pos(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$pos;



implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$pos(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$pos := (if _P && _WRITE_HAS_OCCURRED_$$pos && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$pos);
    return;
}



const _WATCHED_VALUE_$$vel: bv32;

procedure {:inline 1} _LOG_READ_$$vel(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$vel;



implementation {:inline 1} _LOG_READ_$$vel(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$vel := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$vel == _value then true else _READ_HAS_OCCURRED_$$vel);
    return;
}



procedure _CHECK_READ_$$vel(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$vel && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$vel);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$vel && _WATCHED_OFFSET == _offset);



var _WRITE_READ_BENIGN_FLAG_$$vel: bool;

procedure {:inline 1} _LOG_WRITE_$$vel(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$vel, _WRITE_READ_BENIGN_FLAG_$$vel;



implementation {:inline 1} _LOG_WRITE_$$vel(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$vel := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$vel == _value then true else _WRITE_HAS_OCCURRED_$$vel);
    _WRITE_READ_BENIGN_FLAG_$$vel := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$vel == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$vel);
    return;
}



procedure _CHECK_WRITE_$$vel(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$vel && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$vel != _value);
  requires  !(_P && _READ_HAS_OCCURRED_$$vel && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$vel != _value);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$vel && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _LOG_ATOMIC_$$vel(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$vel;



implementation {:inline 1} _LOG_ATOMIC_$$vel(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$vel := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$vel);
    return;
}



procedure _CHECK_ATOMIC_$$vel(_P: bool, _offset: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$vel && _WATCHED_OFFSET == _offset);
  requires  !(_P && _READ_HAS_OCCURRED_$$vel && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$vel(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$vel;



implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$vel(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$vel := (if _P && _WRITE_HAS_OCCURRED_$$vel && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$vel);
    return;
}



const _WATCHED_VALUE_$$newPosition: bv32;

procedure {:inline 1} _LOG_READ_$$newPosition(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$newPosition;



implementation {:inline 1} _LOG_READ_$$newPosition(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$newPosition := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$newPosition == _value then true else _READ_HAS_OCCURRED_$$newPosition);
    return;
}



procedure _CHECK_READ_$$newPosition(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$newPosition && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$newPosition);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$newPosition && _WATCHED_OFFSET == _offset);



var _WRITE_READ_BENIGN_FLAG_$$newPosition: bool;

procedure {:inline 1} _LOG_WRITE_$$newPosition(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$newPosition, _WRITE_READ_BENIGN_FLAG_$$newPosition;



implementation {:inline 1} _LOG_WRITE_$$newPosition(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$newPosition := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$newPosition == _value then true else _WRITE_HAS_OCCURRED_$$newPosition);
    _WRITE_READ_BENIGN_FLAG_$$newPosition := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$newPosition == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$newPosition);
    return;
}



procedure _CHECK_WRITE_$$newPosition(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$newPosition && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$newPosition != _value);
  requires  !(_P && _READ_HAS_OCCURRED_$$newPosition && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$newPosition != _value);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$newPosition && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _LOG_ATOMIC_$$newPosition(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$newPosition;



implementation {:inline 1} _LOG_ATOMIC_$$newPosition(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$newPosition := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$newPosition);
    return;
}



procedure _CHECK_ATOMIC_$$newPosition(_P: bool, _offset: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$newPosition && _WATCHED_OFFSET == _offset);
  requires  !(_P && _READ_HAS_OCCURRED_$$newPosition && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$newPosition(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$newPosition;



implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$newPosition(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$newPosition := (if _P && _WRITE_HAS_OCCURRED_$$newPosition && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$newPosition);
    return;
}



const _WATCHED_VALUE_$$newVelocity: bv32;

procedure {:inline 1} _LOG_READ_$$newVelocity(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$newVelocity;



implementation {:inline 1} _LOG_READ_$$newVelocity(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$newVelocity := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$newVelocity == _value then true else _READ_HAS_OCCURRED_$$newVelocity);
    return;
}



procedure _CHECK_READ_$$newVelocity(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$newVelocity && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$newVelocity);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$newVelocity && _WATCHED_OFFSET == _offset);



var _WRITE_READ_BENIGN_FLAG_$$newVelocity: bool;

procedure {:inline 1} _LOG_WRITE_$$newVelocity(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$newVelocity, _WRITE_READ_BENIGN_FLAG_$$newVelocity;



implementation {:inline 1} _LOG_WRITE_$$newVelocity(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$newVelocity := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$newVelocity == _value then true else _WRITE_HAS_OCCURRED_$$newVelocity);
    _WRITE_READ_BENIGN_FLAG_$$newVelocity := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$newVelocity == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$newVelocity);
    return;
}



procedure _CHECK_WRITE_$$newVelocity(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$newVelocity && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$newVelocity != _value);
  requires  !(_P && _READ_HAS_OCCURRED_$$newVelocity && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$newVelocity != _value);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$newVelocity && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _LOG_ATOMIC_$$newVelocity(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$newVelocity;



implementation {:inline 1} _LOG_ATOMIC_$$newVelocity(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$newVelocity := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$newVelocity);
    return;
}



procedure _CHECK_ATOMIC_$$newVelocity(_P: bool, _offset: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$newVelocity && _WATCHED_OFFSET == _offset);
  requires  !(_P && _READ_HAS_OCCURRED_$$newVelocity && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$newVelocity(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$newVelocity;



implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$newVelocity(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$newVelocity := (if _P && _WRITE_HAS_OCCURRED_$$newVelocity && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$newVelocity);
    return;
}



const _WATCHED_VALUE_$$localPos: bv32;

procedure {:inline 1} _LOG_READ_$$localPos(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$localPos;



implementation {:inline 1} _LOG_READ_$$localPos(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$localPos := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$localPos == _value then true else _READ_HAS_OCCURRED_$$localPos);
    return;
}



procedure _CHECK_READ_$$localPos(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$localPos && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$localPos && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$localPos && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);



var _WRITE_READ_BENIGN_FLAG_$$localPos: bool;

procedure {:inline 1} _LOG_WRITE_$$localPos(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$localPos, _WRITE_READ_BENIGN_FLAG_$$localPos;



implementation {:inline 1} _LOG_WRITE_$$localPos(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$localPos := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$localPos == _value then true else _WRITE_HAS_OCCURRED_$$localPos);
    _WRITE_READ_BENIGN_FLAG_$$localPos := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$localPos == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$localPos);
    return;
}



procedure _CHECK_WRITE_$$localPos(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$localPos && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$localPos != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires  !(_P && _READ_HAS_OCCURRED_$$localPos && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$localPos != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$localPos && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);



procedure {:inline 1} _LOG_ATOMIC_$$localPos(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$localPos;



implementation {:inline 1} _LOG_ATOMIC_$$localPos(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$localPos := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$localPos);
    return;
}



procedure _CHECK_ATOMIC_$$localPos(_P: bool, _offset: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$localPos && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires  !(_P && _READ_HAS_OCCURRED_$$localPos && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);



procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$localPos(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$localPos;



implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$localPos(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$localPos := (if _P && _WRITE_HAS_OCCURRED_$$localPos && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$localPos);
    return;
}



var _TRACKING: bool;

implementation {:inline 1} $bugle_barrier_duplicated_0($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon9_Then, anon9_Else;

  anon9_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$localPos;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$localPos;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$localPos;
    goto anon1;

  anon1:
    goto anon10_Then, anon10_Else;

  anon10_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon3;

  anon3:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$newPosition;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$newPosition;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$newPosition;
    goto anon4;

  anon4:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$newVelocity;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$newVelocity;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$newVelocity;
    goto anon5;

  anon5:
    goto anon11_Then, anon11_Else;

  anon11_Else:
    assume {:partition} !(group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1));
    goto anon8;

  anon8:
    havoc _TRACKING;
    return;

  anon11_Then:
    assume {:partition} group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1);
    havoc $$newPosition;
    goto anon7;

  anon7:
    havoc $$newVelocity;
    goto anon8;

  anon10_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$localPos;
    goto anon3;

  anon9_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}



implementation {:inline 1} $bugle_barrier_duplicated_1($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon9_Then, anon9_Else;

  anon9_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$localPos;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$localPos;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$localPos;
    goto anon1;

  anon1:
    goto anon10_Then, anon10_Else;

  anon10_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon3;

  anon3:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$newPosition;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$newPosition;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$newPosition;
    goto anon4;

  anon4:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$newVelocity;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$newVelocity;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$newVelocity;
    goto anon5;

  anon5:
    goto anon11_Then, anon11_Else;

  anon11_Else:
    assume {:partition} !(group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1));
    goto anon8;

  anon8:
    havoc _TRACKING;
    return;

  anon11_Then:
    assume {:partition} group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1);
    havoc $$newPosition;
    goto anon7;

  anon7:
    havoc $$newVelocity;
    goto anon8;

  anon10_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$localPos;
    goto anon3;

  anon9_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}



function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
