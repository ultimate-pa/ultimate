//#Safe
type _SIZE_T_TYPE = bv32;

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

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;

function {:builtin "bvult"} BV32_ULT(bv32, bv32) : bool;

procedure {:source_name "bar"} $bar($y: bv32) returns ($ret$1: bv32, $ret$2: bv32);
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

implementation {:source_name "bar"} $bar($y: bv32) returns ($ret$1: bv32, $ret$2: bv32)
{
  var $j.0: bv32;
  var $result.0: bv32;
  var $k.0$1: bv32;
  var $k.0$2: bv32;
  var $result.1$1: bv32;
  var $result.1$2: bv32;
  var $w.0$1: bv32;
  var $w.0$2: bv32;
  var $result.2$1: bv32;
  var $result.2$2: bv32;
  var $retval.0$1: bv32;
  var $retval.0$2: bv32;
  var $result.3$1: bv32;
  var $result.3$2: bv32;
  var $q.0$1: bv32;
  var $q.0$2: bv32;
  var v0: bool;
  var v1$1: bool;
  var v1$2: bool;
  var v2$1: bool;
  var v2$2: bool;
  var v3$1: bv32;
  var v3$2: bv32;
  var v4$1: bool;
  var v4$2: bool;
  var v5$1: bool;
  var v5$2: bool;
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

  $entry:
    $j.0, $result.0 := 0bv32, 0bv32;
    p0$1 := false;
    p0$2 := false;
    p7$1 := false;
    p7$2 := false;
    assume {:captureState "loop_entry_state_3_0"} true;
    goto $for.cond;

  $for.cond:
    assume {:captureState "loop_head_state_3"} true;
    assert {:block_sourceloc} {:sourceloc_num 1} true;
    v0 := BV32_SLT($j.0, 100bv32);
    goto $truebb, $falsebb;

  $falsebb:
    assume {:partition} !v0;
    $k.0$1, $result.1$1 := 0bv32, $result.0;
    $k.0$2, $result.1$2 := 0bv32, $result.0;
    p0$1 := true;
    p0$2 := true;
    assume {:captureState "loop_entry_state_1_0"} true;
    goto $for.cond1;

  $for.cond1:
    assume {:captureState "loop_head_state_1"} true;
    assert {:block_sourceloc} {:sourceloc_num 5} p0$1 ==> true;
    v1$1 := (if p0$1 then BV32_SLT($k.0$1, 100bv32) else v1$1);
    v1$2 := (if p0$2 then BV32_SLT($k.0$2, 100bv32) else v1$2);
    p1$1 := false;
    p1$2 := false;
    p2$1 := false;
    p2$2 := false;
    p6$1 := false;
    p6$2 := false;
    p1$1 := (if p0$1 && v1$1 then v1$1 else p1$1);
    p1$2 := (if p0$2 && v1$2 then v1$2 else p1$2);
    p6$1 := (if p0$1 && !v1$1 then !v1$1 else p6$1);
    p6$2 := (if p0$2 && !v1$2 then !v1$2 else p6$2);
    p0$1 := (if p0$1 && !v1$1 then v1$1 else p0$1);
    p0$2 := (if p0$2 && !v1$2 then v1$2 else p0$2);
    $w.0$1, $result.2$1 := (if p1$1 then 0bv32 else $w.0$1), (if p1$1 then BV32_ADD($result.1$1, $k.0$1) else $result.2$1);
    $w.0$2, $result.2$2 := (if p1$2 then 0bv32 else $w.0$2), (if p1$2 then BV32_ADD($result.1$2, $k.0$2) else $result.2$2);
    p2$1 := (if p1$1 then true else p2$1);
    p2$2 := (if p1$2 then true else p2$2);
    assume {:captureState "loop_entry_state_2_0"} true;
    goto $for.cond5;

  $for.cond5:
    assume {:captureState "loop_head_state_2"} true;
    assume {:predicate "p2"} {:dominator_predicate "p1"} true;
    assert p2$1 ==> p0$1;
    assert p2$2 ==> p0$2;
    assert {:block_sourceloc} {:sourceloc_num 7} p2$1 ==> true;
    v2$1 := (if p2$1 then BV32_ULT($w.0$1, local_id_x$1) else v2$1);
    v2$2 := (if p2$2 then BV32_ULT($w.0$2, local_id_x$2) else v2$2);
    p3$1 := false;
    p3$2 := false;
    p4$1 := false;
    p4$2 := false;
    p5$1 := false;
    p5$2 := false;
    p9$1 := false;
    p9$2 := false;
    p3$1 := (if p2$1 && v2$1 then v2$1 else p3$1);
    p3$2 := (if p2$2 && v2$2 then v2$2 else p3$2);
    p5$1 := (if p2$1 && !v2$1 then !v2$1 else p5$1);
    p5$2 := (if p2$2 && !v2$2 then !v2$2 else p5$2);
    p2$1 := (if p2$1 && !v2$1 then v2$1 else p2$1);
    p2$2 := (if p2$2 && !v2$2 then v2$2 else p2$2);
    v3$1 := (if p3$1 then BV32_ADD($result.2$1, $w.0$1) else v3$1);
    v3$2 := (if p3$2 then BV32_ADD($result.2$2, $w.0$2) else v3$2);
    v4$1 := (if p3$1 then BV32_SGT(v3$1, 1000bv32) else v4$1);
    v4$2 := (if p3$2 then BV32_SGT(v3$2, 1000bv32) else v4$2);
    p9$1 := (if p3$1 && v4$1 then v4$1 else p9$1);
    p9$2 := (if p3$2 && v4$2 then v4$2 else p9$2);
    p2$1 := (if p3$1 && v4$1 then !v4$1 else p2$1);
    p2$2 := (if p3$2 && v4$2 then !v4$2 else p2$2);
    p0$1 := (if p3$1 && v4$1 then !v4$1 else p0$1);
    p0$2 := (if p3$2 && v4$2 then !v4$2 else p0$2);
    p4$1 := (if p3$1 && !v4$1 then !v4$1 else p4$1);
    p4$2 := (if p3$2 && !v4$2 then !v4$2 else p4$2);
    $w.0$1, $result.2$1 := (if p4$1 then BV32_ADD($w.0$1, 1bv32) else $w.0$1), (if p4$1 then v3$1 else $result.2$1);
    $w.0$2, $result.2$2 := (if p4$2 then BV32_ADD($w.0$2, 1bv32) else $w.0$2), (if p4$2 then v3$2 else $result.2$2);
    p2$1 := (if p4$1 then true else p2$1);
    p2$2 := (if p4$2 then true else p2$2);
    goto $for.cond5.backedge, $for.cond5.tail;

  $for.cond5.tail:
    assume !p2$1 && !p2$2;
    $k.0$1, $result.1$1 := (if p5$1 then BV32_ADD($k.0$1, 1bv32) else $k.0$1), (if p5$1 then $result.2$1 else $result.1$1);
    $k.0$2, $result.1$2 := (if p5$2 then BV32_ADD($k.0$2, 1bv32) else $k.0$2), (if p5$2 then $result.2$2 else $result.1$2);
    p0$1 := (if p5$1 then true else p0$1);
    p0$2 := (if p5$2 then true else p0$2);
    goto $for.cond1.backedge, $for.cond1.tail;

  $for.cond1.tail:
    assume !p0$1 && !p0$2;
    $result.3$1, $q.0$1 := (if p6$1 then $result.1$1 else $result.3$1), (if p6$1 then 0bv32 else $q.0$1);
    $result.3$2, $q.0$2 := (if p6$2 then $result.1$2 else $result.3$2), (if p6$2 then 0bv32 else $q.0$2);
    p7$1 := (if p6$1 then true else p7$1);
    p7$2 := (if p6$2 then true else p7$2);
    assume {:captureState "loop_entry_state_0_0"} true;
    goto $for.cond16;

  $for.cond16:
    assume {:captureState "loop_head_state_0"} true;
    assume {:predicate "p7"} {:dominator_predicate "p6"} true;
    assert {:block_sourceloc} {:sourceloc_num 15} p7$1 ==> true;
    v5$1 := (if p7$1 then BV32_SLT($q.0$1, 100bv32) else v5$1);
    v5$2 := (if p7$2 then BV32_SLT($q.0$2, 100bv32) else v5$2);
    p8$1 := false;
    p8$2 := false;
    p8$1 := (if p7$1 && v5$1 then v5$1 else p8$1);
    p8$2 := (if p7$2 && v5$2 then v5$2 else p8$2);
    p7$1 := (if p7$1 && !v5$1 then v5$1 else p7$1);
    p7$2 := (if p7$2 && !v5$2 then v5$2 else p7$2);
    $result.3$1, $q.0$1 := (if p8$1 then BV32_ADD($result.3$1, $q.0$1) else $result.3$1), (if p8$1 then BV32_ADD($q.0$1, 1bv32) else $q.0$1);
    $result.3$2, $q.0$2 := (if p8$2 then BV32_ADD($result.3$2, $q.0$2) else $result.3$2), (if p8$2 then BV32_ADD($q.0$2, 1bv32) else $q.0$2);
    p7$1 := (if p8$1 then true else p7$1);
    p7$2 := (if p8$2 then true else p7$2);
    goto $for.cond16.backedge, $for.cond16.tail;

  $for.cond16.tail:
    assume !p7$1 && !p7$2;
    $retval.0$1 := (if p6$1 then $result.3$1 else $retval.0$1);
    $retval.0$2 := (if p6$2 then $result.3$2 else $retval.0$2);
    $retval.0$1 := (if p9$1 then 0bv32 else $retval.0$1);
    $retval.0$2 := (if p9$2 then 0bv32 else $retval.0$2);
    $ret$1 := $retval.0$1;
    $ret$2 := $retval.0$2;
    return;

  $for.cond16.backedge:
    assume {:backedge} p7$1 || p7$2;
    assume {:captureState "loop_back_edge_state_0_0"} true;
    goto $for.cond16;

  $for.cond1.backedge:
    assume {:backedge} p0$1 || p0$2;
    assume {:captureState "loop_back_edge_state_1_0"} true;
    goto $for.cond1;

  $for.cond5.backedge:
    assume {:backedge} p2$1 || p2$2;
    assume {:captureState "loop_back_edge_state_2_0"} true;
    goto $for.cond5;

  $truebb:
    assume {:partition} v0;
    $j.0, $result.0 := BV32_ADD($j.0, 1bv32), BV32_ADD($result.0, $j.0);
    assume {:captureState "loop_back_edge_state_3_0"} true;
    goto $for.cond;
}

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
  var $i.0: bv32;
  var v0: bool;
  var v1$1: bv32;
  var v1$2: bv32;

  $entry:
    $i.0 := 0bv32;
    assume {:captureState "loop_entry_state_4_0"} true;
    goto $for.cond;

  $for.cond:
    assume {:captureState "loop_head_state_4"} true;
    assert {:block_sourceloc} {:sourceloc_num 31} true;
    v0 := BV32_SLT($i.0, 200bv32);
    goto $truebb, $falsebb;

  $falsebb:
    assume {:partition} !v0;
    return;

  $truebb:
    assume {:partition} v0;
    call v1$1, v1$2 := $bar($i.0);
    assume {:captureState "call_return_state_0"} {:procedureName "$bar"} true;
    $i.0 := BV32_ADD($i.0, 1bv32);
    assume {:captureState "loop_back_edge_state_4_0"} true;
    goto $for.cond;
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

var _TRACKING: bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;
