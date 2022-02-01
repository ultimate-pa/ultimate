//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "graph"} {:global} $$graph: [bv32]bv32;

axiom {:array_info "$$graph"} {:global} {:elem_width 32} {:source_name "graph"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$graph: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$graph: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$graph: bool;

var {:source_name "primary_block_buffer"} {:group_shared} $$primary_block_buffer: [bv1][bv32]bv32;

axiom {:array_info "$$primary_block_buffer"} {:group_shared} {:elem_width 32} {:source_name "primary_block_buffer"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$primary_block_buffer: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$primary_block_buffer: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$primary_block_buffer: bool;

const _WATCHED_OFFSET: bv32;

const {:global_offset_x} global_offset_x: bv32;

const {:global_offset_y} global_offset_y: bv32;

const {:global_offset_z} global_offset_z: bv32;

const {:group_id_x} group_id_x$1: bv32;

const {:group_id_x} group_id_x$2: bv32;

const {:group_id_y} group_id_y$1: bv32;

const {:group_id_y} group_id_y$2: bv32;

const {:group_id_z} group_id_z$1: bv32;

const {:group_id_z} group_id_z$2: bv32;

const {:group_size_x} group_size_x: bv32;

const {:group_size_y} group_size_y: bv32;

const {:group_size_z} group_size_z: bv32;

const {:local_id_x} local_id_x$1: bv32;

const {:local_id_x} local_id_x$2: bv32;

const {:local_id_y} local_id_y$1: bv32;

const {:local_id_y} local_id_y$2: bv32;

const {:num_groups_x} num_groups_x: bv32;

const {:num_groups_y} num_groups_y: bv32;

const {:num_groups_z} num_groups_z: bv32;

function __other_bv32(bv32) : bv32;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvand"} BV32_AND(bv32, bv32) : bv32;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;

function {:builtin "bvule"} BV32_ULE(bv32, bv32) : bool;

function {:builtin "bvult"} BV32_ULT(bv32, bv32) : bool;

function {:builtin "zero_extend 31"} BV1_ZEXT32(bv1) : bv32;

procedure {:source_name "transitive_closure_stage1_kernel"} ULTIMATE.start($passnum: bv32);
  requires (if BV32_SGE($passnum, 0bv32) then 1bv1 else 0bv1) != 0bv1;
  requires (if BV32_SLT($passnum, 4096bv32) then 1bv1 else 0bv1) != 0bv1;
  requires !_READ_HAS_OCCURRED_$$graph && !_WRITE_HAS_OCCURRED_$$graph && !_ATOMIC_HAS_OCCURRED_$$graph;
  requires !_READ_HAS_OCCURRED_$$primary_block_buffer && !_WRITE_HAS_OCCURRED_$$primary_block_buffer && !_ATOMIC_HAS_OCCURRED_$$primary_block_buffer;
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
  modifies $$primary_block_buffer, _READ_HAS_OCCURRED_$$graph, _WRITE_HAS_OCCURRED_$$primary_block_buffer, _WRITE_READ_BENIGN_FLAG_$$primary_block_buffer, _WRITE_READ_BENIGN_FLAG_$$primary_block_buffer, $$graph, _TRACKING, _READ_HAS_OCCURRED_$$primary_block_buffer, _WRITE_HAS_OCCURRED_$$graph, _WRITE_READ_BENIGN_FLAG_$$graph, _WRITE_READ_BENIGN_FLAG_$$graph, _TRACKING;

implementation {:source_name "transitive_closure_stage1_kernel"} ULTIMATE.start($passnum: bv32)
{
  var $k.0: bv32;
  var v0$1: bv32;
  var v0$2: bv32;
  var v1$1: bv32;
  var v1$2: bv32;
  var v2$1: bv32;
  var v2$2: bv32;
  var v3: bool;
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
  var v10$1: bv32;
  var v10$2: bv32;
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

  __partitioned_block_$entry_0:
    v0$1 := BV32_ADD(BV32_MUL($passnum, 8bv32), local_id_y$1);
    v0$2 := BV32_ADD(BV32_MUL($passnum, 8bv32), local_id_y$2);
    v1$1 := BV32_ADD(BV32_MUL($passnum, 8bv32), local_id_x$1);
    v1$2 := BV32_ADD(BV32_MUL($passnum, 8bv32), local_id_x$2);
    call _LOG_READ_$$graph(true, BV32_ADD(BV32_MUL(v0$1, 64bv32), v1$1), $$graph[BV32_ADD(BV32_MUL(v0$1, 64bv32), v1$1)]);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 3} true;
    call _CHECK_READ_$$graph(true, BV32_ADD(BV32_MUL(v0$2, 64bv32), v1$2), $$graph[BV32_ADD(BV32_MUL(v0$2, 64bv32), v1$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$graph"} true;
    v2$1 := $$graph[BV32_ADD(BV32_MUL(v0$1, 64bv32), v1$1)];
    v2$2 := $$graph[BV32_ADD(BV32_MUL(v0$2, 64bv32), v1$2)];
    call _LOG_WRITE_$$primary_block_buffer(true, BV32_ADD(BV32_MUL(local_id_y$1, 8bv32), local_id_x$1), v2$1, $$primary_block_buffer[1bv1][BV32_ADD(BV32_MUL(local_id_y$1, 8bv32), local_id_x$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$primary_block_buffer(true, BV32_ADD(BV32_MUL(local_id_y$2, 8bv32), local_id_x$2));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 4} true;
    call _CHECK_WRITE_$$primary_block_buffer(true, BV32_ADD(BV32_MUL(local_id_y$2, 8bv32), local_id_x$2), v2$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$primary_block_buffer"} true;
    $$primary_block_buffer[1bv1][BV32_ADD(BV32_MUL(local_id_y$1, 8bv32), local_id_x$1)] := v2$1;
    $$primary_block_buffer[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(local_id_y$2, 8bv32), local_id_x$2)] := v2$2;
    goto __partitioned_block_$entry_1;

  __partitioned_block_$entry_1:
    call $bugle_barrier_duplicated_0(1bv1, 0bv1);
    $k.0 := 0bv32;
    assume {:captureState "loop_entry_state_0_0"} true;
    goto $for.cond;

  $for.cond:
    assume {:captureState "loop_head_state_0"} true;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _ATOMIC_HAS_OCCURRED_$$primary_block_buffer ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _WRITE_HAS_OCCURRED_$$primary_block_buffer ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _READ_HAS_OCCURRED_$$primary_block_buffer ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:block_sourceloc} {:sourceloc_num 6} true;
    assert {:originated_from_invariant} {:sourceloc_num 7} {:thread 1} (if BV32_AND(BV32_AND(BV1_ZEXT32((if group_id_x$1 == group_id_x$2 then 1bv1 else 0bv1)), BV1_ZEXT32((if group_id_y$1 == group_id_y$2 then 1bv1 else 0bv1))), BV1_ZEXT32((if group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1))) != 0bv32 ==> $k.0 == $k.0 then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 7} {:thread 2} (if BV32_AND(BV32_AND(BV1_ZEXT32((if group_id_x$2 == group_id_x$1 then 1bv1 else 0bv1)), BV1_ZEXT32((if group_id_y$2 == group_id_y$1 then 1bv1 else 0bv1))), BV1_ZEXT32((if group_id_z$2 == group_id_z$1 then 1bv1 else 0bv1))) != 0bv32 ==> $k.0 == $k.0 then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 8} {:thread 1} (if BV32_ULE($k.0, 8bv32) then 1bv1 else 0bv1) != 0bv1;
    v3 := BV32_ULT($k.0, 8bv32);
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
    goto __partitioned_block_$truebb_0, $falsebb;

  $falsebb:
    assume {:partition} !v3;
    call _LOG_READ_$$primary_block_buffer(true, BV32_ADD(BV32_MUL(local_id_y$1, 8bv32), local_id_x$1), $$primary_block_buffer[1bv1][BV32_ADD(BV32_MUL(local_id_y$1, 8bv32), local_id_x$1)]);
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 22} true;
    call _CHECK_READ_$$primary_block_buffer(true, BV32_ADD(BV32_MUL(local_id_y$2, 8bv32), local_id_x$2), $$primary_block_buffer[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(local_id_y$2, 8bv32), local_id_x$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$primary_block_buffer"} true;
    v10$1 := $$primary_block_buffer[1bv1][BV32_ADD(BV32_MUL(local_id_y$1, 8bv32), local_id_x$1)];
    v10$2 := $$primary_block_buffer[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(local_id_y$2, 8bv32), local_id_x$2)];
    call _LOG_WRITE_$$graph(true, BV32_ADD(BV32_MUL(v0$1, 64bv32), v1$1), v10$1, $$graph[BV32_ADD(BV32_MUL(v0$1, 64bv32), v1$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$graph(true, BV32_ADD(BV32_MUL(v0$2, 64bv32), v1$2));
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 23} true;
    call _CHECK_WRITE_$$graph(true, BV32_ADD(BV32_MUL(v0$2, 64bv32), v1$2), v10$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$graph"} true;
    $$graph[BV32_ADD(BV32_MUL(v0$1, 64bv32), v1$1)] := v10$1;
    $$graph[BV32_ADD(BV32_MUL(v0$2, 64bv32), v1$2)] := v10$2;
    return;

  __partitioned_block_$truebb_0:
    assume {:partition} v3;
    call _LOG_READ_$$primary_block_buffer(true, BV32_ADD(BV32_MUL(local_id_y$1, 8bv32), local_id_x$1), $$primary_block_buffer[1bv1][BV32_ADD(BV32_MUL(local_id_y$1, 8bv32), local_id_x$1)]);
    assume {:do_not_predicate} {:check_id "check_state_4"} {:captureState "check_state_4"} {:sourceloc} {:sourceloc_num 10} true;
    call _CHECK_READ_$$primary_block_buffer(true, BV32_ADD(BV32_MUL(local_id_y$2, 8bv32), local_id_x$2), $$primary_block_buffer[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(local_id_y$2, 8bv32), local_id_x$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$primary_block_buffer"} true;
    v4$1 := $$primary_block_buffer[1bv1][BV32_ADD(BV32_MUL(local_id_y$1, 8bv32), local_id_x$1)];
    v4$2 := $$primary_block_buffer[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(local_id_y$2, 8bv32), local_id_x$2)];
    v5$1 := v4$1 == 0bv32;
    v5$2 := v4$2 == 0bv32;
    p1$1 := (if v5$1 then v5$1 else p1$1);
    p1$2 := (if v5$2 then v5$2 else p1$2);
    call _LOG_READ_$$primary_block_buffer(p1$1, BV32_ADD(BV32_MUL(local_id_y$1, 8bv32), $k.0), $$primary_block_buffer[1bv1][BV32_ADD(BV32_MUL(local_id_y$1, 8bv32), $k.0)]);
    assume {:do_not_predicate} {:check_id "check_state_5"} {:captureState "check_state_5"} {:sourceloc} {:sourceloc_num 12} true;
    call _CHECK_READ_$$primary_block_buffer(p1$2, BV32_ADD(BV32_MUL(local_id_y$2, 8bv32), $k.0), $$primary_block_buffer[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(local_id_y$2, 8bv32), $k.0)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$primary_block_buffer"} true;
    v6$1 := (if p1$1 then $$primary_block_buffer[1bv1][BV32_ADD(BV32_MUL(local_id_y$1, 8bv32), $k.0)] else v6$1);
    v6$2 := (if p1$2 then $$primary_block_buffer[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(local_id_y$2, 8bv32), $k.0)] else v6$2);
    v7$1 := (if p1$1 then v6$1 != 0bv32 else v7$1);
    v7$2 := (if p1$2 then v6$2 != 0bv32 else v7$2);
    p3$1 := (if p1$1 && v7$1 then v7$1 else p3$1);
    p3$2 := (if p1$2 && v7$2 then v7$2 else p3$2);
    call _LOG_READ_$$primary_block_buffer(p3$1, BV32_ADD(BV32_MUL($k.0, 8bv32), local_id_x$1), $$primary_block_buffer[1bv1][BV32_ADD(BV32_MUL($k.0, 8bv32), local_id_x$1)]);
    assume {:do_not_predicate} {:check_id "check_state_6"} {:captureState "check_state_6"} {:sourceloc} {:sourceloc_num 14} true;
    call _CHECK_READ_$$primary_block_buffer(p3$2, BV32_ADD(BV32_MUL($k.0, 8bv32), local_id_x$2), $$primary_block_buffer[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL($k.0, 8bv32), local_id_x$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$primary_block_buffer"} true;
    v8$1 := (if p3$1 then $$primary_block_buffer[1bv1][BV32_ADD(BV32_MUL($k.0, 8bv32), local_id_x$1)] else v8$1);
    v8$2 := (if p3$2 then $$primary_block_buffer[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL($k.0, 8bv32), local_id_x$2)] else v8$2);
    v9$1 := (if p3$1 then v8$1 != 0bv32 else v9$1);
    v9$2 := (if p3$2 then v8$2 != 0bv32 else v9$2);
    p5$1 := (if p3$1 && v9$1 then v9$1 else p5$1);
    p5$2 := (if p3$2 && v9$2 then v9$2 else p5$2);
    call _LOG_WRITE_$$primary_block_buffer(p5$1, BV32_ADD(BV32_MUL(local_id_y$1, 8bv32), local_id_x$1), BV32_ADD(BV32_ADD(BV32_MUL($passnum, 8bv32), $k.0), 2bv32), $$primary_block_buffer[1bv1][BV32_ADD(BV32_MUL(local_id_y$1, 8bv32), local_id_x$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$primary_block_buffer(p5$2, BV32_ADD(BV32_MUL(local_id_y$2, 8bv32), local_id_x$2));
    assume {:do_not_predicate} {:check_id "check_state_7"} {:captureState "check_state_7"} {:sourceloc} {:sourceloc_num 16} true;
    call _CHECK_WRITE_$$primary_block_buffer(p5$2, BV32_ADD(BV32_MUL(local_id_y$2, 8bv32), local_id_x$2), BV32_ADD(BV32_ADD(BV32_MUL($passnum, 8bv32), $k.0), 2bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$primary_block_buffer"} true;
    $$primary_block_buffer[1bv1][BV32_ADD(BV32_MUL(local_id_y$1, 8bv32), local_id_x$1)] := (if p5$1 then BV32_ADD(BV32_ADD(BV32_MUL($passnum, 8bv32), $k.0), 2bv32) else $$primary_block_buffer[1bv1][BV32_ADD(BV32_MUL(local_id_y$1, 8bv32), local_id_x$1)]);
    $$primary_block_buffer[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(local_id_y$2, 8bv32), local_id_x$2)] := (if p5$2 then BV32_ADD(BV32_ADD(BV32_MUL($passnum, 8bv32), $k.0), 2bv32) else $$primary_block_buffer[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(local_id_y$2, 8bv32), local_id_x$2)]);
    goto __partitioned_block_$truebb_1;

  __partitioned_block_$truebb_1:
    call $bugle_barrier_duplicated_1(1bv1, 0bv1);
    $k.0 := BV32_ADD($k.0, 1bv32);
    assume {:captureState "loop_back_edge_state_0_0"} true;
    goto $for.cond;
}

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 8bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_y == 8bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_x == 0bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_y == 0bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_z == 0bv32 then 1bv1 else 0bv1) != 0bv1;

const {:local_id_z} local_id_z$1: bv32;

const {:local_id_z} local_id_z$2: bv32;

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_0($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 0bv1;
  modifies $$primary_block_buffer, $$graph, _TRACKING;

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_1($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 0bv1;
  modifies $$primary_block_buffer, $$graph, _TRACKING;

const _WATCHED_VALUE_$$graph: bv32;

procedure {:inline 1} _LOG_READ_$$graph(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$graph;

implementation {:inline 1} _LOG_READ_$$graph(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$graph := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$graph == _value then true else _READ_HAS_OCCURRED_$$graph);
    return;
}

procedure _CHECK_READ_$$graph(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$graph && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$graph);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$graph && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$graph: bool;

procedure {:inline 1} _LOG_WRITE_$$graph(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$graph, _WRITE_READ_BENIGN_FLAG_$$graph;

implementation {:inline 1} _LOG_WRITE_$$graph(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$graph := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$graph == _value then true else _WRITE_HAS_OCCURRED_$$graph);
    _WRITE_READ_BENIGN_FLAG_$$graph := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$graph == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$graph);
    return;
}

procedure _CHECK_WRITE_$$graph(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$graph && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$graph != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$graph && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$graph != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$graph && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$graph(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$graph;

implementation {:inline 1} _LOG_ATOMIC_$$graph(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$graph := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$graph);
    return;
}

procedure _CHECK_ATOMIC_$$graph(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$graph && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$graph && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$graph(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$graph;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$graph(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$graph := (if _P && _WRITE_HAS_OCCURRED_$$graph && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$graph);
    return;
}

const _WATCHED_VALUE_$$primary_block_buffer: bv32;

procedure {:inline 1} _LOG_READ_$$primary_block_buffer(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$primary_block_buffer;

implementation {:inline 1} _LOG_READ_$$primary_block_buffer(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$primary_block_buffer := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$primary_block_buffer == _value then true else _READ_HAS_OCCURRED_$$primary_block_buffer);
    return;
}

procedure _CHECK_READ_$$primary_block_buffer(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$primary_block_buffer && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$primary_block_buffer && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$primary_block_buffer && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$primary_block_buffer: bool;

procedure {:inline 1} _LOG_WRITE_$$primary_block_buffer(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$primary_block_buffer, _WRITE_READ_BENIGN_FLAG_$$primary_block_buffer;

implementation {:inline 1} _LOG_WRITE_$$primary_block_buffer(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$primary_block_buffer := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$primary_block_buffer == _value then true else _WRITE_HAS_OCCURRED_$$primary_block_buffer);
    _WRITE_READ_BENIGN_FLAG_$$primary_block_buffer := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$primary_block_buffer == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$primary_block_buffer);
    return;
}

procedure _CHECK_WRITE_$$primary_block_buffer(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$primary_block_buffer && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$primary_block_buffer != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$primary_block_buffer && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$primary_block_buffer != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$primary_block_buffer && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$primary_block_buffer(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$primary_block_buffer;

implementation {:inline 1} _LOG_ATOMIC_$$primary_block_buffer(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$primary_block_buffer := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$primary_block_buffer);
    return;
}

procedure _CHECK_ATOMIC_$$primary_block_buffer(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$primary_block_buffer && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$primary_block_buffer && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$primary_block_buffer(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$primary_block_buffer;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$primary_block_buffer(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$primary_block_buffer := (if _P && _WRITE_HAS_OCCURRED_$$primary_block_buffer && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$primary_block_buffer);
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
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$primary_block_buffer;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$primary_block_buffer;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$primary_block_buffer;
    goto anon1;

  anon1:
    goto anon8_Then, anon8_Else;

  anon8_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon3;

  anon3:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$graph;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$graph;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$graph;
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
    havoc $$graph;
    goto anon6;

  anon8_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$primary_block_buffer;
    goto anon3;

  anon7_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

implementation {:inline 1} $bugle_barrier_duplicated_1($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon7_Then, anon7_Else;

  anon7_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$primary_block_buffer;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$primary_block_buffer;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$primary_block_buffer;
    goto anon1;

  anon1:
    goto anon8_Then, anon8_Else;

  anon8_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon3;

  anon3:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$graph;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$graph;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$graph;
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
    havoc $$graph;
    goto anon6;

  anon8_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$primary_block_buffer;
    goto anon3;

  anon7_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;
