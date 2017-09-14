//#Safe
type _SIZE_T_TYPE = bv32;

const _WATCHED_OFFSET: bv32;

const {:__enabled} __enabled: bool;

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

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvand"} BV32_AND(bv32, bv32) : bv32;

function {:builtin "bvugt"} BV32_UGT(bv32, bv32) : bool;

function {:builtin "bvult"} BV32_ULT(bv32, bv32) : bool;

function {:builtin "zero_extend 31"} BV1_ZEXT32(bv1) : bv32;

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
  var $j.0$1: bv32;
  var $j.0$2: bv32;
  var $i.0$1: bv32;
  var $i.0$2: bv32;
  var v0$1: bool;
  var v0$2: bool;
  var v1$1: bool;
  var v1$2: bool;
  var v2$1: bool;
  var v2$2: bool;
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

  $entry:
    $j.0$1 := 0bv32;
    $j.0$2 := 0bv32;
    p0$1 := false;
    p0$2 := false;
    p0$1 := true;
    p0$2 := true;
    assume {:captureState "loop_entry_state_0_0"} true;
    goto $for.cond;

  $for.cond:
    assume {:captureState "loop_head_state_0"} true;
    assert {:block_sourceloc} {:sourceloc_num 1} p0$1 ==> true;
    v0$1 := (if p0$1 then BV32_ULT($j.0$1, group_id_x$1) else v0$1);
    v0$2 := (if p0$2 then BV32_ULT($j.0$2, group_id_x$2) else v0$2);
    p1$1 := false;
    p1$2 := false;
    p2$1 := false;
    p2$2 := false;
    p3$1 := false;
    p3$2 := false;
    p4$1 := false;
    p4$2 := false;
    p6$1 := false;
    p6$2 := false;
    p1$1 := (if p0$1 && v0$1 then v0$1 else p1$1);
    p1$2 := (if p0$2 && v0$2 then v0$2 else p1$2);
    p0$1 := (if p0$1 && !v0$1 then v0$1 else p0$1);
    p0$2 := (if p0$2 && !v0$2 then v0$2 else p0$2);
    v1$1 := (if p1$1 then BV32_UGT($j.0$1, local_id_x$1) else v1$1);
    v1$2 := (if p1$2 then BV32_UGT($j.0$2, local_id_x$2) else v1$2);
    p3$1 := (if p1$1 && v1$1 then v1$1 else p3$1);
    p3$2 := (if p1$2 && v1$2 then v1$2 else p3$2);
    $i.0$1 := (if p3$1 then 0bv32 else $i.0$1);
    $i.0$2 := (if p3$2 then 0bv32 else $i.0$2);
    p4$1 := (if p3$1 then true else p4$1);
    p4$2 := (if p3$2 then true else p4$2);
    assume {:captureState "loop_entry_state_1_0"} true;
    goto $for.cond3;

  $for.cond3:
    assume {:captureState "loop_head_state_1"} true;
    assume {:predicate "p4"} {:dominator_predicate "p3"} true;
    assert p4$1 ==> p0$1;
    assert p4$2 ==> p0$2;
    assert {:block_sourceloc} {:sourceloc_num 4} p4$1 ==> true;
    v2$1 := (if p4$1 then BV32_ULT($i.0$1, group_id_x$1) else v2$1);
    v2$2 := (if p4$2 then BV32_ULT($i.0$2, group_id_x$2) else v2$2);
    p5$1 := false;
    p5$2 := false;
    p5$1 := (if p4$1 && v2$1 then v2$1 else p5$1);
    p5$2 := (if p4$2 && v2$2 then v2$2 else p5$2);
    p4$1 := (if p4$1 && !v2$1 then v2$1 else p4$1);
    p4$2 := (if p4$2 && !v2$2 then v2$2 else p4$2);
    assert {:do_not_predicate} {:sourceloc_num 6} {:thread 1} (if BV32_AND(BV32_AND(BV1_ZEXT32((if BV32_ULT($j.0$1, group_id_x$1) then 1bv1 else 0bv1)), BV1_ZEXT32((if BV32_UGT($j.0$1, local_id_x$1) then 1bv1 else 0bv1))), BV1_ZEXT32((if BV32_ULT($i.0$1, group_id_x$1) then 1bv1 else 0bv1))) != 0bv32 ==> p5$1 then 1bv1 else 0bv1) != 0bv1;
    assert {:do_not_predicate} {:sourceloc_num 6} {:thread 2} (if BV32_AND(BV32_AND(BV1_ZEXT32((if BV32_ULT($j.0$2, group_id_x$2) then 1bv1 else 0bv1)), BV1_ZEXT32((if BV32_UGT($j.0$2, local_id_x$2) then 1bv1 else 0bv1))), BV1_ZEXT32((if BV32_ULT($i.0$2, group_id_x$2) then 1bv1 else 0bv1))) != 0bv32 ==> p5$2 then 1bv1 else 0bv1) != 0bv1;
    $i.0$1 := (if p5$1 then BV32_ADD($i.0$1, 1bv32) else $i.0$1);
    $i.0$2 := (if p5$2 then BV32_ADD($i.0$2, 1bv32) else $i.0$2);
    p4$1 := (if p5$1 then true else p4$1);
    p4$2 := (if p5$2 then true else p4$2);
    goto $for.cond3.backedge, $for.cond3.tail;

  $for.cond3.tail:
    assume !p4$1 && !p4$2;
    $j.0$1 := (if p1$1 then BV32_ADD($j.0$1, 1bv32) else $j.0$1);
    $j.0$2 := (if p1$2 then BV32_ADD($j.0$2, 1bv32) else $j.0$2);
    p0$1 := (if p1$1 then true else p0$1);
    p0$2 := (if p1$2 then true else p0$2);
    goto $for.cond.backedge, $for.cond.tail;

  $for.cond.tail:
    assume !p0$1 && !p0$2;
    return;

  $for.cond.backedge:
    assume {:backedge} p0$1 || p0$2;
    assume {:captureState "loop_back_edge_state_0_0"} true;
    goto $for.cond;

  $for.cond3.backedge:
    assume {:backedge} p4$1 || p4$2;
    assume {:captureState "loop_back_edge_state_1_0"} true;
    goto $for.cond3;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 32bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 32bv32 then 1bv1 else 0bv1) != 0bv1;

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

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
