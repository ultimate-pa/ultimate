//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "d_Result"} {:global} $$d_Result: [bv32]bv32;

axiom {:array_info "$$d_Result"} {:global} {:elem_width 32} {:source_name "d_Result"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$d_Result: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$d_Result: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$d_Result: bool;

var {:source_name "s_Hist"} {:group_shared} $$_ZZ1kPjE6s_Hist: [bv1][bv32]bv32;

axiom {:array_info "$$_ZZ1kPjE6s_Hist"} {:group_shared} {:elem_width 32} {:source_name "s_Hist"} {:source_elem_width 32} {:source_dimensions "4096"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist: bool;

const _WATCHED_OFFSET: bv32;

const {:__enabled} __enabled: bool;

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

function __other_bool(bool) : bool;

function __other_bv32(bv32) : bv32;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvand"} BV32_AND(bv32, bv32) : bv32;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvsle"} BV32_SLE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;

function {:builtin "bvsub"} BV32_SUB(bv32, bv32) : bv32;

function {:builtin "bvudiv"} BV32_UDIV(bv32, bv32) : bv32;

function {:builtin "bvult"} BV32_ULT(bv32, bv32) : bool;

function {:builtin "bvurem"} BV32_UREM(bv32, bv32) : bv32;

function {:builtin "zero_extend 31"} BV1_ZEXT32(bv1) : bv32;

procedure {:source_name "k"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$d_Result && !_WRITE_HAS_OCCURRED_$$d_Result && !_ATOMIC_HAS_OCCURRED_$$d_Result;
  requires !_READ_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist && !_WRITE_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist && !_ATOMIC_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist;
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
  modifies $$_ZZ1kPjE6s_Hist, $$d_Result, _TRACKING, _READ_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist, _WRITE_HAS_OCCURRED_$$d_Result, _WRITE_READ_BENIGN_FLAG_$$d_Result, _WRITE_READ_BENIGN_FLAG_$$d_Result, _WRITE_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist, _WRITE_READ_BENIGN_FLAG_$$_ZZ1kPjE6s_Hist, _WRITE_READ_BENIGN_FLAG_$$_ZZ1kPjE6s_Hist;

implementation {:source_name "k"} ULTIMATE.start()
{
  var $i.0: bv32;
  var $i15.0$1: bv32;
  var $i15.0$2: bv32;
  var $sum.0$1: bv32;
  var $sum.0$2: bv32;
  var $accumPos.0$1: bv32;
  var $accumPos.0$2: bv32;
  var $accumPos.1$1: bv32;
  var $accumPos.1$2: bv32;
  var v0: bool;
  var v1$1: bool;
  var v1$2: bool;
  var v2$1: bool;
  var v2$2: bool;
  var v3$1: bv32;
  var v3$2: bv32;
  var v5$1: bool;
  var v5$2: bool;
  var v4$1: bv32;
  var v4$2: bv32;
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

  $entry:
    $i.0 := 0bv32;
    p1$1 := false;
    p1$2 := false;
    assume {:captureState "loop_entry_state_1_0"} true;
    goto $for.cond;

  $for.cond:
    assume {:captureState "loop_head_state_1"} true;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _ATOMIC_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _WRITE_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _READ_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:block_sourceloc} {:sourceloc_num 1} true;
    assert {:originated_from_invariant} {:sourceloc_num 2} {:thread 1} (if BV1_ZEXT32((if true then 1bv1 else 0bv1)) == BV1_ZEXT32((if true then 1bv1 else 0bv1)) then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 3} {:thread 1} (if $i.0 == $i.0 then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 4} {:thread 1} (if BV32_SGE($i.0, 0bv32) then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 5} {:thread 1} (if _WRITE_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist ==> BV32_SUB(BV32_UREM(BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32), 64bv32), local_id_x$1) == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    v0 := BV32_SLT($i.0, 16bv32);
    p0$1 := false;
    p0$2 := false;
    p5$1 := false;
    p5$2 := false;
    goto $truebb, __partitioned_block_$falsebb_0;

  __partitioned_block_$falsebb_0:
    assume {:partition} !v0;
    goto __partitioned_block_$falsebb_1;

  __partitioned_block_$falsebb_1:
    call $bugle_barrier_duplicated_0(1bv1, 1bv1);
    v1$1 := BV32_ULT(local_id_x$1, 64bv32);
    v1$2 := BV32_ULT(local_id_x$2, 64bv32);
    p0$1 := (if v1$1 then v1$1 else p0$1);
    p0$2 := (if v1$2 then v1$2 else p0$2);
    $i15.0$1, $sum.0$1, $accumPos.0$1 := (if p0$1 then 0bv32 else $i15.0$1), (if p0$1 then 0bv32 else $sum.0$1), (if p0$1 then BV32_MUL(BV32_AND(local_id_x$1, 15bv32), 4bv32) else $accumPos.0$1);
    $i15.0$2, $sum.0$2, $accumPos.0$2 := (if p0$2 then 0bv32 else $i15.0$2), (if p0$2 then 0bv32 else $sum.0$2), (if p0$2 then BV32_MUL(BV32_AND(local_id_x$2, 15bv32), 4bv32) else $accumPos.0$2);
    p1$1 := (if p0$1 then true else p1$1);
    p1$2 := (if p0$2 then true else p1$2);
    assume {:captureState "loop_entry_state_0_0"} true;
    goto $for.cond16;

  $for.cond16:
    assume {:captureState "loop_head_state_0"} true;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _ATOMIC_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _WRITE_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _READ_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assume {:predicate "p1"} {:dominator_predicate "p0"} true;
    assert {:block_sourceloc} {:sourceloc_num 12} p1$1 ==> true;
    assert {:originated_from_invariant} {:sourceloc_num 13} {:thread 1} p1$1 ==> (if BV32_AND(BV1_ZEXT32((if BV32_SLE(0bv32, $accumPos.0$1) then 1bv1 else 0bv1)), BV1_ZEXT32((if BV32_SLT($accumPos.0$1, 64bv32) then 1bv1 else 0bv1))) != 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 13} {:thread 2} p1$2 ==> (if BV32_AND(BV1_ZEXT32((if BV32_SLE(0bv32, $accumPos.0$2) then 1bv1 else 0bv1)), BV1_ZEXT32((if BV32_SLT($accumPos.0$2, 64bv32) then 1bv1 else 0bv1))) != 0bv32 then 1bv1 else 0bv1) != 0bv1;
    v2$1 := (if p1$1 then BV32_SLT($i15.0$1, 64bv32) else v2$1);
    v2$2 := (if p1$2 then BV32_SLT($i15.0$2, 64bv32) else v2$2);
    p2$1 := false;
    p2$2 := false;
    p3$1 := false;
    p3$2 := false;
    p4$1 := false;
    p4$2 := false;
    p2$1 := (if p1$1 && v2$1 then v2$1 else p2$1);
    p2$2 := (if p1$2 && v2$2 then v2$2 else p2$2);
    p1$1 := (if p1$1 && !v2$1 then v2$1 else p1$1);
    p1$2 := (if p1$2 && !v2$2 then v2$2 else p1$2);
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 15} true;
    v3$1 := (if p2$1 then $$_ZZ1kPjE6s_Hist[1bv1][BV32_ADD(BV32_MUL(local_id_x$1, 64bv32), $accumPos.0$1)] else v3$1);
    v3$2 := (if p2$2 then $$_ZZ1kPjE6s_Hist[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(local_id_x$2, 64bv32), $accumPos.0$2)] else v3$2);
    v4$1 := (if p2$1 then BV32_ADD($accumPos.0$1, 1bv32) else v4$1);
    v4$2 := (if p2$2 then BV32_ADD($accumPos.0$2, 1bv32) else v4$2);
    v5$1 := (if p2$1 then v4$1 == 64bv32 else v5$1);
    v5$2 := (if p2$2 then v4$2 == 64bv32 else v5$2);
    p4$1 := (if p2$1 && v5$1 then v5$1 else p4$1);
    p4$2 := (if p2$2 && v5$2 then v5$2 else p4$2);
    p3$1 := (if p2$1 && !v5$1 then !v5$1 else p3$1);
    p3$2 := (if p2$2 && !v5$2 then !v5$2 else p3$2);
    $accumPos.1$1 := (if p3$1 then v4$1 else $accumPos.1$1);
    $accumPos.1$2 := (if p3$2 then v4$2 else $accumPos.1$2);
    $accumPos.1$1 := (if p4$1 then 0bv32 else $accumPos.1$1);
    $accumPos.1$2 := (if p4$2 then 0bv32 else $accumPos.1$2);
    $i15.0$1, $sum.0$1, $accumPos.0$1 := (if p2$1 then BV32_ADD($i15.0$1, 1bv32) else $i15.0$1), (if p2$1 then BV32_ADD($sum.0$1, v3$1) else $sum.0$1), (if p2$1 then $accumPos.1$1 else $accumPos.0$1);
    $i15.0$2, $sum.0$2, $accumPos.0$2 := (if p2$2 then BV32_ADD($i15.0$2, 1bv32) else $i15.0$2), (if p2$2 then BV32_ADD($sum.0$2, v3$2) else $sum.0$2), (if p2$2 then $accumPos.1$2 else $accumPos.0$2);
    p1$1 := (if p2$1 then true else p1$1);
    p1$2 := (if p2$2 then true else p1$2);
    goto $for.cond16.backedge, $for.cond16.tail;

  $for.cond16.tail:
    assume !p1$1 && !p1$2;
    call _LOG_WRITE_$$d_Result(p0$1, BV32_ADD(BV32_MUL(group_id_x$1, 64bv32), local_id_x$1), $sum.0$1, $$d_Result[BV32_ADD(BV32_MUL(group_id_x$1, 64bv32), local_id_x$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$d_Result(p0$2, BV32_ADD(BV32_MUL(group_id_x$2, 64bv32), local_id_x$2));
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 20} true;
    call _CHECK_WRITE_$$d_Result(p0$2, BV32_ADD(BV32_MUL(group_id_x$2, 64bv32), local_id_x$2), $sum.0$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$d_Result"} true;
    $$d_Result[BV32_ADD(BV32_MUL(group_id_x$1, 64bv32), local_id_x$1)] := (if p0$1 then $sum.0$1 else $$d_Result[BV32_ADD(BV32_MUL(group_id_x$1, 64bv32), local_id_x$1)]);
    $$d_Result[BV32_ADD(BV32_MUL(group_id_x$2, 64bv32), local_id_x$2)] := (if p0$2 then $sum.0$2 else $$d_Result[BV32_ADD(BV32_MUL(group_id_x$2, 64bv32), local_id_x$2)]);
    return;

  $for.cond16.backedge:
    assume {:backedge} p1$1 || p1$2;
    assume {:captureState "loop_back_edge_state_0_0"} true;
    goto $for.cond16;

  $truebb:
    assume {:partition} v0;
    call _LOG_WRITE_$$_ZZ1kPjE6s_Hist(true, BV32_ADD(local_id_x$1, BV32_MUL($i.0, 64bv32)), 0bv32, $$_ZZ1kPjE6s_Hist[1bv1][BV32_ADD(local_id_x$1, BV32_MUL($i.0, 64bv32))]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$_ZZ1kPjE6s_Hist(true, BV32_ADD(local_id_x$2, BV32_MUL($i.0, 64bv32)));
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 7} true;
    call _CHECK_WRITE_$$_ZZ1kPjE6s_Hist(true, BV32_ADD(local_id_x$2, BV32_MUL($i.0, 64bv32)), 0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$_ZZ1kPjE6s_Hist"} true;
    $$_ZZ1kPjE6s_Hist[1bv1][BV32_ADD(local_id_x$1, BV32_MUL($i.0, 64bv32))] := 0bv32;
    $$_ZZ1kPjE6s_Hist[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(local_id_x$2, BV32_MUL($i.0, 64bv32))] := 0bv32;
    $i.0 := BV32_ADD($i.0, 1bv32);
    assume {:captureState "loop_back_edge_state_1_0"} true;
    goto $for.cond;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 64bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 64bv32 then 1bv1 else 0bv1) != 0bv1;

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
  requires $1 == 1bv1;
  modifies $$_ZZ1kPjE6s_Hist, $$d_Result, _TRACKING;

const _WATCHED_VALUE_$$d_Result: bv32;

procedure {:inline 1} _LOG_READ_$$d_Result(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$d_Result;

implementation {:inline 1} _LOG_READ_$$d_Result(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$d_Result := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$d_Result == _value then true else _READ_HAS_OCCURRED_$$d_Result);
    return;
}

procedure _CHECK_READ_$$d_Result(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$d_Result && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$d_Result);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$d_Result && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$d_Result: bool;

procedure {:inline 1} _LOG_WRITE_$$d_Result(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$d_Result, _WRITE_READ_BENIGN_FLAG_$$d_Result;

implementation {:inline 1} _LOG_WRITE_$$d_Result(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$d_Result := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$d_Result == _value then true else _WRITE_HAS_OCCURRED_$$d_Result);
    _WRITE_READ_BENIGN_FLAG_$$d_Result := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$d_Result == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$d_Result);
    return;
}

procedure _CHECK_WRITE_$$d_Result(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$d_Result && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$d_Result != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$d_Result && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$d_Result != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$d_Result && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$d_Result(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$d_Result;

implementation {:inline 1} _LOG_ATOMIC_$$d_Result(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$d_Result := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$d_Result);
    return;
}

procedure _CHECK_ATOMIC_$$d_Result(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$d_Result && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$d_Result && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$d_Result(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$d_Result;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$d_Result(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$d_Result := (if _P && _WRITE_HAS_OCCURRED_$$d_Result && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$d_Result);
    return;
}

const _WATCHED_VALUE_$$_ZZ1kPjE6s_Hist: bv32;

procedure {:inline 1} _LOG_READ_$$_ZZ1kPjE6s_Hist(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist;

implementation {:inline 1} _LOG_READ_$$_ZZ1kPjE6s_Hist(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ1kPjE6s_Hist == _value then true else _READ_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist);
    return;
}

procedure _CHECK_READ_$$_ZZ1kPjE6s_Hist(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$_ZZ1kPjE6s_Hist && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$_ZZ1kPjE6s_Hist: bool;

procedure {:inline 1} _LOG_WRITE_$$_ZZ1kPjE6s_Hist(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist, _WRITE_READ_BENIGN_FLAG_$$_ZZ1kPjE6s_Hist;

implementation {:inline 1} _LOG_WRITE_$$_ZZ1kPjE6s_Hist(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ1kPjE6s_Hist == _value then true else _WRITE_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist);
    _WRITE_READ_BENIGN_FLAG_$$_ZZ1kPjE6s_Hist := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ1kPjE6s_Hist == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$_ZZ1kPjE6s_Hist);
    return;
}

procedure _CHECK_WRITE_$$_ZZ1kPjE6s_Hist(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ1kPjE6s_Hist != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ1kPjE6s_Hist != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$_ZZ1kPjE6s_Hist(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist;

implementation {:inline 1} _LOG_ATOMIC_$$_ZZ1kPjE6s_Hist(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist);
    return;
}

procedure _CHECK_ATOMIC_$$_ZZ1kPjE6s_Hist(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$_ZZ1kPjE6s_Hist(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$_ZZ1kPjE6s_Hist;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$_ZZ1kPjE6s_Hist(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$_ZZ1kPjE6s_Hist := (if _P && _WRITE_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$_ZZ1kPjE6s_Hist);
    return;
}

var _TRACKING: bool;

implementation {:inline 1} $bugle_barrier_duplicated_0($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon7_Then, anon7_Else;

  anon7_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$_ZZ1kPjE6s_Hist;
    goto anon1;

  anon1:
    goto anon8_Then, anon8_Else;

  anon8_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon3;

  anon3:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$d_Result;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$d_Result;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$d_Result;
    goto anon4;

  anon4:
    goto anon9_Then, anon9_Else;

  anon9_Else:
    assume {:partition} !(group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1));
    goto anon6;

  anon6:
    havoc _TRACKING;
    return;

  anon9_Then:
    assume {:partition} group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && ($1 != 0bv1 || $1 != 0bv1);
    havoc $$d_Result;
    goto anon6;

  anon8_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$_ZZ1kPjE6s_Hist;
    goto anon3;

  anon7_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;
