//#Safe
type _SIZE_T_TYPE = bv32;

const _WATCHED_OFFSET: bv32;

const {:group_size_x} group_size_x: bv32;

const {:group_size_y} group_size_y: bv32;

const {:group_size_z} group_size_z: bv32;

const {:num_groups_x} num_groups_x: bv32;

const {:num_groups_y} num_groups_y: bv32;

const {:num_groups_z} num_groups_z: bv32;

procedure {:source_name "crazy"} ULTIMATE.start();
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

implementation {:source_name "crazy"} ULTIMATE.start()
{
  var v0$1: bv32;
  var v0$2: bv32;
  var v1$1: bool;
  var v1$2: bool;
  var v2$1: bv32;
  var v2$2: bv32;
  var v3$1: bool;
  var v3$2: bool;
  var v4$1: bv32;
  var v4$2: bv32;
  var v5$1: bool;
  var v5$2: bool;
  var v6$1: bv32;
  var v6$2: bv32;
  var v7$1: bool;
  var v7$2: bool;
  var v8$1: bv32;
  var v8$2: bv32;
  var v9$1: bool;
  var v9$2: bool;
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

  $entry:
    call v0$1, v0$2 := $_Z6nondetv(true, true);
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z6nondetv"} true;
    v1$1 := v0$1 != 0bv32;
    v1$2 := v0$2 != 0bv32;
    p0$1 := false;
    p0$2 := false;
    p1$1 := false;
    p1$2 := false;
    p2$1 := false;
    p2$2 := false;
    p2$1 := (if !v1$1 then !v1$1 else p2$1);
    p2$2 := (if !v1$2 then !v1$2 else p2$2);
    p2$1 := (if p1$1 then true else p2$1);
    p2$2 := (if p1$2 then true else p2$2);
    assume {:captureState "loop_entry_state_0_0"} true;
    goto $while.cond;

  $while.cond:
    assume {:captureState "loop_head_state_0"} true;
    assume {:predicate "p2"} {:dominator_predicate "p1"} true;
    assert {:block_sourceloc} {:sourceloc_num 4} p2$1 ==> true;
    call v2$1, v2$2 := $_Z6nondetv(p2$1, p2$2);
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z6nondetv"} true;
    v3$1 := (if p2$1 then v2$1 != 0bv32 else v3$1);
    v3$2 := (if p2$2 then v2$2 != 0bv32 else v3$2);
    p3$1 := false;
    p3$2 := false;
    p4$1 := false;
    p4$2 := false;
    p4$1 := (if p2$1 && v3$1 then v3$1 else p4$1);
    p4$2 := (if p2$2 && v3$2 then v3$2 else p4$2);
    p2$1 := (if p2$1 && !v3$1 then v3$1 else p2$1);
    p2$2 := (if p2$2 && !v3$2 then v3$2 else p2$2);
    p4$1 := (if p3$1 then true else p4$1);
    p4$2 := (if p3$2 then true else p4$2);
    assume {:captureState "loop_entry_state_1_0"} true;
    goto $while.cond3;

  $while.cond3:
    assume {:captureState "loop_head_state_1"} true;
    assume {:predicate "p4"} {:dominator_predicate "p3"} true;
    assert p4$1 ==> p2$1;
    assert p4$2 ==> p2$2;
    assert {:block_sourceloc} {:sourceloc_num 7} p4$1 ==> true;
    call v4$1, v4$2 := $_Z6nondetv(p4$1, p4$2);
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z6nondetv"} true;
    v5$1 := (if p4$1 then v4$1 != 0bv32 else v5$1);
    v5$2 := (if p4$2 then v4$2 != 0bv32 else v5$2);
    p5$1 := false;
    p5$2 := false;
    p6$1 := false;
    p6$2 := false;
    p10$1 := false;
    p10$2 := false;
    p6$1 := (if p4$1 && v5$1 then v5$1 else p6$1);
    p6$2 := (if p4$2 && v5$2 then v5$2 else p6$2);
    p4$1 := (if p4$1 && !v5$1 then v5$1 else p4$1);
    p4$2 := (if p4$2 && !v5$2 then v5$2 else p4$2);
    p6$1 := (if p5$1 then true else p6$1);
    p6$2 := (if p5$2 then true else p6$2);
    assume {:captureState "loop_entry_state_2_0"} true;
    goto $while.cond7;

  $while.cond7:
    assume {:captureState "loop_head_state_2"} true;
    assume {:predicate "p6"} {:dominator_predicate "p5"} true;
    assert p6$1 ==> p4$1;
    assert p6$2 ==> p4$2;
    assert p4$1 ==> p2$1;
    assert p4$2 ==> p2$2;
    assert {:block_sourceloc} {:sourceloc_num 10} p6$1 ==> true;
    call v6$1, v6$2 := $_Z6nondetv(p6$1, p6$2);
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z6nondetv"} true;
    v7$1 := (if p6$1 then v6$1 != 0bv32 else v7$1);
    v7$2 := (if p6$2 then v6$2 != 0bv32 else v7$2);
    p7$1 := false;
    p7$2 := false;
    p8$1 := false;
    p8$2 := false;
    p9$1 := false;
    p9$2 := false;
    p11$1 := false;
    p11$2 := false;
    p7$1 := (if p6$1 && v7$1 then v7$1 else p7$1);
    p7$2 := (if p6$2 && v7$2 then v7$2 else p7$2);
    p4$1 := (if p6$1 && !v7$1 then !v7$1 else p4$1);
    p4$2 := (if p6$2 && !v7$2 then !v7$2 else p4$2);
    p6$1 := (if p6$1 && !v7$1 then v7$1 else p6$1);
    p6$2 := (if p6$2 && !v7$2 then v7$2 else p6$2);
    call v8$1, v8$2 := $_Z6nondetv(p7$1, p7$2);
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z6nondetv"} true;
    v9$1 := (if p7$1 then v8$1 != 0bv32 else v9$1);
    v9$2 := (if p7$2 then v8$2 != 0bv32 else v9$2);
    p6$1 := (if p7$1 && v9$1 then !v9$1 else p6$1);
    p6$2 := (if p7$2 && v9$2 then !v9$2 else p6$2);
    p4$1 := (if p7$1 && v9$1 then !v9$1 else p4$1);
    p4$2 := (if p7$2 && v9$2 then !v9$2 else p4$2);
    p6$1 := (if p7$1 && !v9$1 then !v9$1 else p6$1);
    p6$2 := (if p7$2 && !v9$2 then !v9$2 else p6$2);
    p6$1 := (if p8$1 then true else p6$1);
    p6$2 := (if p8$2 then true else p6$2);
    goto $while.cond7.backedge, $while.cond7.tail;

  $while.cond7.tail:
    assume !p6$1 && !p6$2;
    p4$1 := (if p9$1 then true else p4$1);
    p4$2 := (if p9$2 then true else p4$2);
    goto $while.cond3.backedge, $while.cond3.tail;

  $while.cond3.tail:
    assume !p4$1 && !p4$2;
    p2$1 := (if p3$1 then true else p2$1);
    p2$2 := (if p3$2 then true else p2$2);
    goto $while.cond.backedge, $while.cond.tail;

  $while.cond.tail:
    assume !p2$1 && !p2$2;
    return;

  $while.cond.backedge:
    assume {:backedge} p2$1 || p2$2;
    assume {:captureState "loop_back_edge_state_0_0"} true;
    goto $while.cond;

  $while.cond3.backedge:
    assume {:backedge} p4$1 || p4$2;
    assume {:captureState "loop_back_edge_state_1_0"} true;
    goto $while.cond3;

  $while.cond7.backedge:
    assume {:backedge} p6$1 || p6$2;
    assume {:captureState "loop_back_edge_state_2_0"} true;
    goto $while.cond7;
}

procedure {:source_name "_Z6nondetv"} $_Z6nondetv(_P$1: bool, _P$2: bool) returns ($ret$1: bv32, $ret$2: bv32);

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 2bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 1bv32 then 1bv1 else 0bv1) != 0bv1;

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

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
