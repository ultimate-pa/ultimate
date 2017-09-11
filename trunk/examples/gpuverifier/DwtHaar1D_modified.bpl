type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);



axiom {:array_info "$$inSignal"} {:global} {:elem_width 32} {:source_name "inSignal"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$inSignal: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$inSignal: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$inSignal: bool;

var {:source_name "coefsSignal"} {:global} $$coefsSignal: [bv32]bv32;

axiom {:array_info "$$coefsSignal"} {:global} {:elem_width 32} {:source_name "coefsSignal"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$coefsSignal: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$coefsSignal: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$coefsSignal: bool;

var {:source_name "AverageSignal"} {:global} $$AverageSignal: [bv32]bv32;

axiom {:array_info "$$AverageSignal"} {:global} {:elem_width 32} {:source_name "AverageSignal"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$AverageSignal: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$AverageSignal: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$AverageSignal: bool;

var {:source_name "sharedArray"} {:group_shared} $$sharedArray: [bv1][bv32]bv32;

axiom {:array_info "$$sharedArray"} {:group_shared} {:elem_width 32} {:source_name "sharedArray"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$sharedArray: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$sharedArray: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$sharedArray: bool;

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

function UI32_TO_FP32(bv32) : bv32;

function {:bvbuiltin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:bvbuiltin "bvand"} BV32_AND(bv32, bv32) : bv32;

function {:bvbuiltin "bvlshr"} BV32_LSHR(bv32, bv32) : bv32;

function {:bvbuiltin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

function {:bvbuiltin "bvsdiv"} BV32_SDIV(bv32, bv32) : bv32;

function {:bvbuiltin "bvshl"} BV32_SHL(bv32, bv32) : bv32;

function {:bvbuiltin "bvsub"} BV32_SUB(bv32, bv32) : bv32;

function {:bvbuiltin "bvudiv"} BV32_UDIV(bv32, bv32) : bv32;

function {:bvbuiltin "bvuge"} BV32_UGE(bv32, bv32) : bool;

function {:bvbuiltin "bvugt"} BV32_UGT(bv32, bv32) : bool;

function {:bvbuiltin "bvult"} BV32_ULT(bv32, bv32) : bool;

function {:bvbuiltin "bvxor"} BV1_XOR(bv1, bv1) : bv1;

procedure {:source_name "dwtHaar1D"} {:kernel} ULTIMATE.start($tLevels: bv32, $signalLength: bv32, $levelsDone: bv32, $mLevels: bv32);
  requires  (if $signalLength == 1024bv32 then 1bv1 else 0bv1) != 0bv1;
  requires  (if $tLevels == 6bv32 then 1bv1 else 0bv1) != 0bv1;
  requires  (if $mLevels == 8bv32 then 1bv1 else 0bv1) != 0bv1;
  requires !_READ_HAS_OCCURRED_$$inSignal && !_WRITE_HAS_OCCURRED_$$inSignal && !_ATOMIC_HAS_OCCURRED_$$inSignal;
  requires !_READ_HAS_OCCURRED_$$coefsSignal && !_WRITE_HAS_OCCURRED_$$coefsSignal && !_ATOMIC_HAS_OCCURRED_$$coefsSignal;
  requires !_READ_HAS_OCCURRED_$$AverageSignal && !_WRITE_HAS_OCCURRED_$$AverageSignal && !_ATOMIC_HAS_OCCURRED_$$AverageSignal;
  requires !_READ_HAS_OCCURRED_$$sharedArray && !_WRITE_HAS_OCCURRED_$$sharedArray && !_ATOMIC_HAS_OCCURRED_$$sharedArray;
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
  modifies $$sharedArray, _WRITE_HAS_OCCURRED_$$sharedArray, _WRITE_READ_BENIGN_FLAG_$$sharedArray, _WRITE_READ_BENIGN_FLAG_$$sharedArray, $$coefsSignal, $$AverageSignal, _TRACKING, _READ_HAS_OCCURRED_$$sharedArray, _WRITE_HAS_OCCURRED_$$AverageSignal, _WRITE_READ_BENIGN_FLAG_$$AverageSignal, _WRITE_READ_BENIGN_FLAG_$$AverageSignal, _TRACKING, _WRITE_HAS_OCCURRED_$$coefsSignal, _WRITE_READ_BENIGN_FLAG_$$coefsSignal, _WRITE_READ_BENIGN_FLAG_$$coefsSignal, _TRACKING;



implementation {:source_name "dwtHaar1D"} {:kernel} ULTIMATE.start($tLevels: bv32, $signalLength: bv32, $levelsDone: bv32, $mLevels: bv32)
{
  var $t0.0$1: bv32;
  var $t0.0$2: bv32;
  var $t1.0$1: bv32;
  var $t1.0$2: bv32;
  var $cond: bv32;
  var $activeThreads.0: bv32;
  var $midOutPos.0$1: bv32;
  var $midOutPos.0$2: bv32;
  var $i.0: bv32;
  var $data0.0$1: bv32;
  var $data0.0$2: bv32;
  var $data1.0$1: bv32;
  var $data1.0$2: bv32;
  var $data0.1$1: bv32;
  var $data0.1$2: bv32;
  var $data1.1$1: bv32;
  var $data1.1$2: bv32;
  var $midOutPos.1$1: bv32;
  var $midOutPos.1$2: bv32;
  var v1$1: bv32;
  var v1$2: bv32;
  var v0$1: bv32;
  var v0$2: bv32;
  var v2: bv32;
  var v3$1: bv32;
  var v3$2: bv32;
  var v5: bool;
  var v4$1: bv32;
  var v4$2: bv32;
  var v6: bv32;
  var v7: bool;
  var v8: bv32;
  var v10$1: bv32;
  var v10$2: bv32;
  var v9$1: bv32;
  var v9$2: bv32;
  var v11: bool;
  var v12$1: bool;
  var v12$2: bool;
  var v13$1: bv32;
  var v13$2: bv32;
  var v14$1: bv32;
  var v14$2: bv32;
  var v15$1: bool;
  var v15$2: bool;
  var v16$1: bool;
  var v16$2: bool;
  var v17$1: bv32;
  var v17$2: bv32;
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
    v0$1 := local_id_x$1;
    v0$2 := local_id_x$2;
    v1$1 := group_id_x$1;
    v1$2 := group_id_x$2;
    v2 := group_size_x;
    havoc v3$1, v3$2;
    havoc v4$1, v4$2;
    v5 := 0bv32 == $levelsDone;
    goto $truebb, $falsebb;

  $falsebb:
    assume {:partition} !v5;
    $t0.0$1, $t1.0$1 := v3$1, v4$1;
    $t0.0$2, $t1.0$2 := v3$2, v4$2;
    goto __partitioned_block_$if.end_0;

  __partitioned_block_$if.end_0:
    call  _LOG_WRITE_$$sharedArray(true, v0$1, $t0.0$1, $$sharedArray[1bv1][v0$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$sharedArray(true, v0$2);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 8} true;
    call  _CHECK_WRITE_$$sharedArray(true, v0$2, $t0.0$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$sharedArray"} true;
    $$sharedArray[1bv1][v0$1] := $t0.0$1;
    $$sharedArray[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v0$2] := $t0.0$2;
    call  _LOG_WRITE_$$sharedArray(true, BV32_ADD(v2, v0$1), $t1.0$1, $$sharedArray[1bv1][BV32_ADD(v2, v0$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$sharedArray(true, BV32_ADD(v2, v0$2));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 9} true;
    call  _CHECK_WRITE_$$sharedArray(true, BV32_ADD(v2, v0$2), $t1.0$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$sharedArray"} true;
    $$sharedArray[1bv1][BV32_ADD(v2, v0$1)] := $t1.0$1;
    $$sharedArray[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(v2, v0$2)] := $t1.0$2;
    goto __partitioned_block_$if.end_1;

  __partitioned_block_$if.end_1:
    call  $bugle_barrier_duplicated_0(1bv1, 0bv1);
    v7 := BV32_UGT($tLevels, $mLevels);
    goto $truebb0, $falsebb0;

  $falsebb0:
    assume {:partition} !v7;
    $cond := $tLevels;
    goto $cond.end;

  $cond.end:
    v8 := FDIV32(1065353216bv32, FSQRT32(1073741824bv32));
    havoc v9$1, v9$2;
    havoc v10$1, v10$2;
    $activeThreads.0, $midOutPos.0$1, $i.0, $data0.0$1, $data1.0$1 := BV32_SDIV(BV32_SHL(1bv32, BV32_AND($cond, 31bv32)), 2bv32), BV32_UDIV($signalLength, 2bv32), 0bv32, v9$1, v10$1;
    $midOutPos.0$2, $data0.0$2, $data1.0$2 := BV32_UDIV($signalLength, 2bv32), v9$2, v10$2;
    assume {:captureState "loop_entry_state_0_0"} true;
    goto $for.cond;

  $for.cond:
    assume {:captureState "loop_head_state_0"} true;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _ATOMIC_HAS_OCCURRED_$$sharedArray ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _WRITE_HAS_OCCURRED_$$sharedArray ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _READ_HAS_OCCURRED_$$sharedArray ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:block_sourceloc} {:sourceloc_num 14} true;
    assert {:originated_from_invariant} {:sourceloc_num 15} {:thread 1} (if $activeThreads.0 == BV32_SDIV(BV32_SHL(1bv32, BV32_AND(BV32_SUB($cond, $i.0), 31bv32)), 2bv32) then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 16} {:thread 1} (if BV32_ULT(v0$1, $activeThreads.0) ==> $midOutPos.0$1 == BV32_LSHR(BV32_UDIV($signalLength, 2bv32), BV32_AND($i.0, 31bv32)) then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 16} {:thread 2} (if BV32_ULT(v0$2, $activeThreads.0) ==> $midOutPos.0$2 == BV32_LSHR(BV32_UDIV($signalLength, 2bv32), BV32_AND($i.0, 31bv32)) then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 17} {:thread 1} (if _WRITE_HAS_OCCURRED_$$coefsSignal ==> BV32_UGE(BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32), BV32_ADD(BV32_ADD(BV32_SHL($midOutPos.0$1, 1bv32), BV32_MUL(v1$1, BV32_SHL($activeThreads.0, 1bv32))), v0$1)) then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 18} {:thread 1} (if BV32_UGE(v0$1, 16bv32) ==> _WRITE_HAS_OCCURRED_$$coefsSignal ==> BV32_UGE(BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32), BV32_ADD(BV32_ADD(512bv32, BV32_MUL(v1$1, 32bv32)), v0$1)) then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 19} {:thread 1} (if BV32_UGE(v0$1, 8bv32) ==> _WRITE_HAS_OCCURRED_$$coefsSignal ==> BV32_UGE(BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32), BV32_ADD(BV32_ADD(256bv32, BV32_MUL(v1$1, 16bv32)), v0$1)) then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 20} {:thread 1} (if BV32_UGE(v0$1, 4bv32) ==> _WRITE_HAS_OCCURRED_$$coefsSignal ==> BV32_UGE(BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32), BV32_ADD(BV32_ADD(128bv32, BV32_MUL(v1$1, 8bv32)), v0$1)) then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 21} {:thread 1} (if BV32_UGE(v0$1, 2bv32) ==> _WRITE_HAS_OCCURRED_$$coefsSignal ==> BV32_UGE(BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32), BV32_ADD(BV32_ADD(64bv32, BV32_MUL(v1$1, 4bv32)), v0$1)) then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 22} {:thread 1} (if BV32_UGE(v0$1, 1bv32) ==> _WRITE_HAS_OCCURRED_$$coefsSignal ==> BV32_UGE(BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32), BV32_ADD(BV32_ADD(32bv32, BV32_MUL(v1$1, 2bv32)), v0$1)) then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 23} {:thread 1} (if BV32_UGE(v0$1, BV32_SDIV(BV32_SHL(1bv32, BV32_AND($cond, 31bv32)), 2bv32)) ==> BV1_XOR((if _WRITE_HAS_OCCURRED_$$coefsSignal then 1bv1 else 0bv1), 1bv1) == 1bv1 then 1bv1 else 0bv1) != 0bv1;
    v11 := BV32_ULT($i.0, $cond);
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
    goto __partitioned_block_$truebb1_0, $falsebb1;

  $falsebb1:
    assume {:partition} !v11;
    v16$1 := 0bv32 == v0$1;
    v16$2 := 0bv32 == v0$2;
    p4$1 := (if v16$1 then v16$1 else p4$1);
    p4$2 := (if v16$2 then v16$2 else p4$2);
    call  _LOG_READ_$$sharedArray(p4$1, 0bv32, $$sharedArray[1bv1][0bv32]);
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 38} true;
    call  _CHECK_READ_$$sharedArray(p4$2, 0bv32, $$sharedArray[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][0bv32]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$sharedArray"} true;
    v17$1 := (if p4$1 then $$sharedArray[1bv1][0bv32] else v17$1);
    v17$2 := (if p4$2 then $$sharedArray[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][0bv32] else v17$2);
    call  _LOG_WRITE_$$AverageSignal(p4$1, v1$1, v17$1, $$AverageSignal[v1$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$AverageSignal(p4$2, v1$2);
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 39} true;
    call  _CHECK_WRITE_$$AverageSignal(p4$2, v1$2, v17$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$AverageSignal"} true;
    $$AverageSignal[v1$1] := (if p4$1 then v17$1 else $$AverageSignal[v1$1]);
    $$AverageSignal[v1$2] := (if p4$2 then v17$2 else $$AverageSignal[v1$2]);
    return;

  __partitioned_block_$truebb1_0:
    assume {:partition} v11;
    v12$1 := BV32_ULT(v0$1, $activeThreads.0);
    v12$2 := BV32_ULT(v0$2, $activeThreads.0);
    p1$1 := (if v12$1 then v12$1 else p1$1);
    p1$2 := (if v12$2 then v12$2 else p1$2);
    p0$1 := (if !v12$1 then !v12$1 else p0$1);
    p0$2 := (if !v12$2 then !v12$2 else p0$2);
    $data0.1$1, $data1.1$1 := (if p0$1 then $data0.0$1 else $data0.1$1), (if p0$1 then $data1.0$1 else $data1.1$1);
    $data0.1$2, $data1.1$2 := (if p0$2 then $data0.0$2 else $data0.1$2), (if p0$2 then $data1.0$2 else $data1.1$2);
    call  _LOG_READ_$$sharedArray(p1$1, BV32_MUL(2bv32, v0$1), $$sharedArray[1bv1][BV32_MUL(2bv32, v0$1)]);
    assume {:do_not_predicate} {:check_id "check_state_6"} {:captureState "check_state_6"} {:sourceloc} {:sourceloc_num 26} true;
    call  _CHECK_READ_$$sharedArray(p1$2, BV32_MUL(2bv32, v0$2), $$sharedArray[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_MUL(2bv32, v0$2)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$sharedArray"} true;
    v13$1 := (if p1$1 then $$sharedArray[1bv1][BV32_MUL(2bv32, v0$1)] else v13$1);
    v13$2 := (if p1$2 then $$sharedArray[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_MUL(2bv32, v0$2)] else v13$2);
    call  _LOG_READ_$$sharedArray(p1$1, BV32_ADD(BV32_MUL(2bv32, v0$1), 1bv32), $$sharedArray[1bv1][BV32_ADD(BV32_MUL(2bv32, v0$1), 1bv32)]);
    assume {:do_not_predicate} {:check_id "check_state_7"} {:captureState "check_state_7"} {:sourceloc} {:sourceloc_num 27} true;
    call  _CHECK_READ_$$sharedArray(p1$2, BV32_ADD(BV32_MUL(2bv32, v0$2), 1bv32), $$sharedArray[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(2bv32, v0$2), 1bv32)]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$sharedArray"} true;
    v14$1 := (if p1$1 then $$sharedArray[1bv1][BV32_ADD(BV32_MUL(2bv32, v0$1), 1bv32)] else v14$1);
    v14$2 := (if p1$2 then $$sharedArray[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(2bv32, v0$2), 1bv32)] else v14$2);
    $data0.1$1, $data1.1$1 := (if p1$1 then v13$1 else $data0.1$1), (if p1$1 then v14$1 else $data1.1$1);
    $data0.1$2, $data1.1$2 := (if p1$2 then v13$2 else $data0.1$2), (if p1$2 then v14$2 else $data1.1$2);
    goto __partitioned_block_$truebb1_1;

  __partitioned_block_$truebb1_1:
    call  $bugle_barrier_duplicated_1(1bv1, 0bv1);
    v15$1 := BV32_ULT(v0$1, $activeThreads.0);
    v15$2 := BV32_ULT(v0$2, $activeThreads.0);
    p3$1 := (if v15$1 then v15$1 else p3$1);
    p3$2 := (if v15$2 then v15$2 else p3$2);
    p2$1 := (if !v15$1 then !v15$1 else p2$1);
    p2$2 := (if !v15$2 then !v15$2 else p2$2);
    $midOutPos.1$1 := (if p2$1 then $midOutPos.0$1 else $midOutPos.1$1);
    $midOutPos.1$2 := (if p2$2 then $midOutPos.0$2 else $midOutPos.1$2);
    call  _LOG_WRITE_$$sharedArray(p3$1, v0$1, FMUL32(FADD32($data0.1$1, $data1.1$1), v8), $$sharedArray[1bv1][v0$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$sharedArray(p3$2, v0$2);
    assume {:do_not_predicate} {:check_id "check_state_4"} {:captureState "check_state_4"} {:sourceloc} {:sourceloc_num 31} true;
    call  _CHECK_WRITE_$$sharedArray(p3$2, v0$2, FMUL32(FADD32($data0.1$2, $data1.1$2), v8));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$sharedArray"} true;
    $$sharedArray[1bv1][v0$1] := (if p3$1 then FMUL32(FADD32($data0.1$1, $data1.1$1), v8) else $$sharedArray[1bv1][v0$1]);
    $$sharedArray[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v0$2] := (if p3$2 then FMUL32(FADD32($data0.1$2, $data1.1$2), v8) else $$sharedArray[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][v0$2]);
    call  _LOG_WRITE_$$coefsSignal(p3$1, BV32_ADD(BV32_ADD($midOutPos.0$1, BV32_MUL(v1$1, $activeThreads.0)), v0$1), FMUL32(FSUB32($data0.1$1, $data1.1$1), v8), $$coefsSignal[BV32_ADD(BV32_ADD($midOutPos.0$1, BV32_MUL(v1$1, $activeThreads.0)), v0$1)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$coefsSignal(p3$2, BV32_ADD(BV32_ADD($midOutPos.0$2, BV32_MUL(v1$2, $activeThreads.0)), v0$2));
    assume {:do_not_predicate} {:check_id "check_state_5"} {:captureState "check_state_5"} {:sourceloc} {:sourceloc_num 32} true;
    call  _CHECK_WRITE_$$coefsSignal(p3$2, BV32_ADD(BV32_ADD($midOutPos.0$2, BV32_MUL(v1$2, $activeThreads.0)), v0$2), FMUL32(FSUB32($data0.1$2, $data1.1$2), v8));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$coefsSignal"} true;
    $$coefsSignal[BV32_ADD(BV32_ADD($midOutPos.0$1, BV32_MUL(v1$1, $activeThreads.0)), v0$1)] := (if p3$1 then FMUL32(FSUB32($data0.1$1, $data1.1$1), v8) else $$coefsSignal[BV32_ADD(BV32_ADD($midOutPos.0$1, BV32_MUL(v1$1, $activeThreads.0)), v0$1)]);
    $$coefsSignal[BV32_ADD(BV32_ADD($midOutPos.0$2, BV32_MUL(v1$2, $activeThreads.0)), v0$2)] := (if p3$2 then FMUL32(FSUB32($data0.1$2, $data1.1$2), v8) else $$coefsSignal[BV32_ADD(BV32_ADD($midOutPos.0$2, BV32_MUL(v1$2, $activeThreads.0)), v0$2)]);
    $midOutPos.1$1 := (if p3$1 then BV32_LSHR($midOutPos.0$1, 1bv32) else $midOutPos.1$1);
    $midOutPos.1$2 := (if p3$2 then BV32_LSHR($midOutPos.0$2, 1bv32) else $midOutPos.1$2);
    goto __partitioned_block_$truebb1_2;

  __partitioned_block_$truebb1_2:
    call  $bugle_barrier_duplicated_2(1bv1, 0bv1);
    $activeThreads.0, $midOutPos.0$1, $i.0, $data0.0$1, $data1.0$1 := BV32_LSHR($activeThreads.0, 1bv32), $midOutPos.1$1, BV32_ADD($i.0, 1bv32), $data0.1$1, $data1.1$1;
    $midOutPos.0$2, $data0.0$2, $data1.0$2 := $midOutPos.1$2, $data0.1$2, $data1.1$2;
    assume {:captureState "loop_back_edge_state_0_0"} true;
    goto $for.cond;

  $truebb0:
    assume {:partition} v7;
    $cond := $mLevels;
    goto $cond.end;

  $truebb:
    assume {:partition} v5;
    v6 := FDIV32(1065353216bv32, FSQRT32(UI32_TO_FP32($signalLength)));
    $t0.0$1, $t1.0$1 := FMUL32(v3$1, v6), FMUL32(v4$1, v6);
    $t0.0$2, $t1.0$2 := FMUL32(v3$2, v6), FMUL32(v4$2, v6);
    goto __partitioned_block_$if.end_0;
}



axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 512bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 2bv32 then 1bv1 else 0bv1) != 0bv1;

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
  modifies $$sharedArray, $$coefsSignal, $$AverageSignal, _TRACKING;



procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_1($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 0bv1;
  modifies $$sharedArray, $$coefsSignal, $$AverageSignal, _TRACKING;



procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_2($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 0bv1;
  modifies $$sharedArray, $$coefsSignal, $$AverageSignal, _TRACKING;



const _WATCHED_VALUE_$$inSignal: bv32;

procedure {:inline 1} _LOG_READ_$$inSignal(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$inSignal;



implementation {:inline 1} _LOG_READ_$$inSignal(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$inSignal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$inSignal == _value then true else _READ_HAS_OCCURRED_$$inSignal);
    return;
}



procedure _CHECK_READ_$$inSignal(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$inSignal && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$inSignal);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$inSignal && _WATCHED_OFFSET == _offset);



var _WRITE_READ_BENIGN_FLAG_$$inSignal: bool;

procedure {:inline 1} _LOG_WRITE_$$inSignal(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$inSignal, _WRITE_READ_BENIGN_FLAG_$$inSignal;



implementation {:inline 1} _LOG_WRITE_$$inSignal(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$inSignal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$inSignal == _value then true else _WRITE_HAS_OCCURRED_$$inSignal);
    _WRITE_READ_BENIGN_FLAG_$$inSignal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$inSignal == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$inSignal);
    return;
}



procedure _CHECK_WRITE_$$inSignal(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$inSignal && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$inSignal != _value);
  requires  !(_P && _READ_HAS_OCCURRED_$$inSignal && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$inSignal != _value);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$inSignal && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _LOG_ATOMIC_$$inSignal(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$inSignal;



implementation {:inline 1} _LOG_ATOMIC_$$inSignal(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$inSignal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$inSignal);
    return;
}



procedure _CHECK_ATOMIC_$$inSignal(_P: bool, _offset: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$inSignal && _WATCHED_OFFSET == _offset);
  requires  !(_P && _READ_HAS_OCCURRED_$$inSignal && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$inSignal(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$inSignal;



implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$inSignal(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$inSignal := (if _P && _WRITE_HAS_OCCURRED_$$inSignal && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$inSignal);
    return;
}



const _WATCHED_VALUE_$$coefsSignal: bv32;

procedure {:inline 1} _LOG_READ_$$coefsSignal(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$coefsSignal;



implementation {:inline 1} _LOG_READ_$$coefsSignal(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$coefsSignal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$coefsSignal == _value then true else _READ_HAS_OCCURRED_$$coefsSignal);
    return;
}



procedure _CHECK_READ_$$coefsSignal(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$coefsSignal && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$coefsSignal);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$coefsSignal && _WATCHED_OFFSET == _offset);



var _WRITE_READ_BENIGN_FLAG_$$coefsSignal: bool;

procedure {:inline 1} _LOG_WRITE_$$coefsSignal(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$coefsSignal, _WRITE_READ_BENIGN_FLAG_$$coefsSignal;



implementation {:inline 1} _LOG_WRITE_$$coefsSignal(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$coefsSignal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$coefsSignal == _value then true else _WRITE_HAS_OCCURRED_$$coefsSignal);
    _WRITE_READ_BENIGN_FLAG_$$coefsSignal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$coefsSignal == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$coefsSignal);
    return;
}



procedure _CHECK_WRITE_$$coefsSignal(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$coefsSignal && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$coefsSignal != _value);
  requires  !(_P && _READ_HAS_OCCURRED_$$coefsSignal && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$coefsSignal != _value);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$coefsSignal && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _LOG_ATOMIC_$$coefsSignal(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$coefsSignal;



implementation {:inline 1} _LOG_ATOMIC_$$coefsSignal(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$coefsSignal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$coefsSignal);
    return;
}



procedure _CHECK_ATOMIC_$$coefsSignal(_P: bool, _offset: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$coefsSignal && _WATCHED_OFFSET == _offset);
  requires  !(_P && _READ_HAS_OCCURRED_$$coefsSignal && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$coefsSignal(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$coefsSignal;



implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$coefsSignal(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$coefsSignal := (if _P && _WRITE_HAS_OCCURRED_$$coefsSignal && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$coefsSignal);
    return;
}



const _WATCHED_VALUE_$$AverageSignal: bv32;

procedure {:inline 1} _LOG_READ_$$AverageSignal(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$AverageSignal;



implementation {:inline 1} _LOG_READ_$$AverageSignal(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$AverageSignal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$AverageSignal == _value then true else _READ_HAS_OCCURRED_$$AverageSignal);
    return;
}



procedure _CHECK_READ_$$AverageSignal(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$AverageSignal && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$AverageSignal);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$AverageSignal && _WATCHED_OFFSET == _offset);



var _WRITE_READ_BENIGN_FLAG_$$AverageSignal: bool;

procedure {:inline 1} _LOG_WRITE_$$AverageSignal(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$AverageSignal, _WRITE_READ_BENIGN_FLAG_$$AverageSignal;



implementation {:inline 1} _LOG_WRITE_$$AverageSignal(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$AverageSignal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$AverageSignal == _value then true else _WRITE_HAS_OCCURRED_$$AverageSignal);
    _WRITE_READ_BENIGN_FLAG_$$AverageSignal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$AverageSignal == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$AverageSignal);
    return;
}



procedure _CHECK_WRITE_$$AverageSignal(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$AverageSignal && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$AverageSignal != _value);
  requires  !(_P && _READ_HAS_OCCURRED_$$AverageSignal && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$AverageSignal != _value);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$AverageSignal && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _LOG_ATOMIC_$$AverageSignal(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$AverageSignal;



implementation {:inline 1} _LOG_ATOMIC_$$AverageSignal(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$AverageSignal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$AverageSignal);
    return;
}



procedure _CHECK_ATOMIC_$$AverageSignal(_P: bool, _offset: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$AverageSignal && _WATCHED_OFFSET == _offset);
  requires  !(_P && _READ_HAS_OCCURRED_$$AverageSignal && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$AverageSignal(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$AverageSignal;



implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$AverageSignal(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$AverageSignal := (if _P && _WRITE_HAS_OCCURRED_$$AverageSignal && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$AverageSignal);
    return;
}



const _WATCHED_VALUE_$$sharedArray: bv32;

procedure {:inline 1} _LOG_READ_$$sharedArray(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$sharedArray;



implementation {:inline 1} _LOG_READ_$$sharedArray(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$sharedArray := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$sharedArray == _value then true else _READ_HAS_OCCURRED_$$sharedArray);
    return;
}



procedure _CHECK_READ_$$sharedArray(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$sharedArray && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$sharedArray && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$sharedArray && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);



var _WRITE_READ_BENIGN_FLAG_$$sharedArray: bool;

procedure {:inline 1} _LOG_WRITE_$$sharedArray(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$sharedArray, _WRITE_READ_BENIGN_FLAG_$$sharedArray;



implementation {:inline 1} _LOG_WRITE_$$sharedArray(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$sharedArray := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$sharedArray == _value then true else _WRITE_HAS_OCCURRED_$$sharedArray);
    _WRITE_READ_BENIGN_FLAG_$$sharedArray := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$sharedArray == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$sharedArray);
    return;
}



procedure _CHECK_WRITE_$$sharedArray(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$sharedArray && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$sharedArray != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires  !(_P && _READ_HAS_OCCURRED_$$sharedArray && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$sharedArray != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$sharedArray && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);



procedure {:inline 1} _LOG_ATOMIC_$$sharedArray(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$sharedArray;



implementation {:inline 1} _LOG_ATOMIC_$$sharedArray(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$sharedArray := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$sharedArray);
    return;
}



procedure _CHECK_ATOMIC_$$sharedArray(_P: bool, _offset: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$sharedArray && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires  !(_P && _READ_HAS_OCCURRED_$$sharedArray && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);



procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$sharedArray(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$sharedArray;



implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$sharedArray(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$sharedArray := (if _P && _WRITE_HAS_OCCURRED_$$sharedArray && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$sharedArray);
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
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$sharedArray;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$sharedArray;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$sharedArray;
    goto anon1;

  anon1:
    goto anon10_Then, anon10_Else;

  anon10_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon3;

  anon3:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$coefsSignal;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$coefsSignal;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$coefsSignal;
    goto anon4;

  anon4:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$AverageSignal;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$AverageSignal;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$AverageSignal;
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
    havoc $$coefsSignal;
    goto anon7;

  anon7:
    havoc $$AverageSignal;
    goto anon8;

  anon10_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$sharedArray;
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
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$sharedArray;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$sharedArray;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$sharedArray;
    goto anon1;

  anon1:
    goto anon10_Then, anon10_Else;

  anon10_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon3;

  anon3:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$coefsSignal;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$coefsSignal;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$coefsSignal;
    goto anon4;

  anon4:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$AverageSignal;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$AverageSignal;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$AverageSignal;
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
    havoc $$coefsSignal;
    goto anon7;

  anon7:
    havoc $$AverageSignal;
    goto anon8;

  anon10_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$sharedArray;
    goto anon3;

  anon9_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}



implementation {:inline 1} $bugle_barrier_duplicated_2($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon9_Then, anon9_Else;

  anon9_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$sharedArray;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$sharedArray;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$sharedArray;
    goto anon1;

  anon1:
    goto anon10_Then, anon10_Else;

  anon10_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon3;

  anon3:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$coefsSignal;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$coefsSignal;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$coefsSignal;
    goto anon4;

  anon4:
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_READ_HAS_OCCURRED_$$AverageSignal;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$AverageSignal;
    assume group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> $1 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$AverageSignal;
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
    havoc $$coefsSignal;
    goto anon7;

  anon7:
    havoc $$AverageSignal;
    goto anon8;

  anon10_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$sharedArray;
    goto anon3;

  anon9_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}



function {:bvbuiltin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:bvbuiltin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:bvbuiltin "bvslt"} BV32_SLT(bv32, bv32) : bool;
