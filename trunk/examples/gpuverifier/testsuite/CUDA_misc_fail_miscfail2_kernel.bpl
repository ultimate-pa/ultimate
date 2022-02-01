//#Unsafe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

axiom {:array_info "$$volMat"} {:global} {:elem_width 32} {:source_name "volMat"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$volMat: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$volMat: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$volMat: bool;

axiom {:array_info "$$driftMat"} {:global} {:elem_width 32} {:source_name "driftMat"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$driftMat: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$driftMat: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$driftMat: bool;

axiom {:array_info "$$f0"} {:global} {:elem_width 32} {:source_name "f0"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$f0: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$f0: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$f0: bool;

axiom {:array_info "$$f_j"} {:elem_width 32} {:source_name "f_j"} {:source_elem_width 32} {:source_dimensions "1"} true;

var {:source_name "sdata"} {:group_shared} $$_ZZ9helloCUDAiifffiiPfS_S_E5sdata: [bv1][bv32]bv32;

axiom {:array_info "$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata"} {:group_shared} {:elem_width 32} {:source_name "sdata"} {:source_elem_width 32} {:source_dimensions "8192"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata: bool;

const _WATCHED_OFFSET: bv32;

const {:group_size_x} group_size_x: bv32;

const {:group_size_y} group_size_y: bv32;

const {:group_size_z} group_size_z: bv32;

const {:local_id_x} local_id_x$1: bv32;

const {:local_id_x} local_id_x$2: bv32;

const {:num_groups_x} num_groups_x: bv32;

const {:num_groups_y} num_groups_y: bv32;

const {:num_groups_z} num_groups_z: bv32;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

function {:builtin "bvsdiv"} BV32_SDIV(bv32, bv32) : bv32;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;

function {:builtin "bvsrem"} BV32_SREM(bv32, bv32) : bv32;

function {:builtin "bvudiv"} BV32_UDIV(bv32, bv32) : bv32;

function {:builtin "bvult"} BV32_ULT(bv32, bv32) : bool;

function {:builtin "bvurem"} BV32_UREM(bv32, bv32) : bv32;

function {:builtin "bvxor"} BV1_XOR(bv1, bv1) : bv1;

procedure {:source_name "helloCUDA"} ULTIMATE.start($num32PathPerBlock: bv32, $callPutFlag: bv32, $faceValue: bv32, $strike: bv32, $dt: bv32, $actualTimeSteps: bv32, $numTimeOffsets: bv32);
  requires (if $numTimeOffsets == 143bv32 then 1bv1 else 0bv1) != 0bv1;
  requires (if $actualTimeSteps == 13bv32 then 1bv1 else 0bv1) != 0bv1;
  requires !_READ_HAS_OCCURRED_$$volMat && !_WRITE_HAS_OCCURRED_$$volMat && !_ATOMIC_HAS_OCCURRED_$$volMat;
  requires !_READ_HAS_OCCURRED_$$driftMat && !_WRITE_HAS_OCCURRED_$$driftMat && !_ATOMIC_HAS_OCCURRED_$$driftMat;
  requires !_READ_HAS_OCCURRED_$$f0 && !_WRITE_HAS_OCCURRED_$$f0 && !_ATOMIC_HAS_OCCURRED_$$f0;
  requires !_READ_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata && !_WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata && !_ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata;
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
  modifies $$_ZZ9helloCUDAiifffiiPfS_S_E5sdata, _TRACKING, _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata, _TRACKING, _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata, _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata, _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata;

implementation {:source_name "helloCUDA"} ULTIMATE.start($num32PathPerBlock: bv32, $callPutFlag: bv32, $faceValue: bv32, $strike: bv32, $dt: bv32, $actualTimeSteps: bv32, $numTimeOffsets: bv32)
{
  var $j.0: bv32;
  var v0: bool;
  var v1$1: bv32;
  var v1$2: bv32;
  var v2$1: bv32;
  var v2$2: bv32;

  $entry:
    call $bugle_barrier_duplicated_0(1bv1, 1bv1);
    $j.0 := 0bv32;
    assume {:captureState "loop_entry_state_0_0"} true;
    goto $for.cond;

  $for.cond:
    assume {:captureState "loop_head_state_0"} true;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:tag "groupSharedArraysDisjointAcrossGroups"} _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2;
    assert {:block_sourceloc} {:sourceloc_num 4} true;
    assert {:originated_from_invariant} {:sourceloc_num 5} {:thread 1} (if _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata ==> BV32_UREM(BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32), group_size_x) == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 6} {:thread 1} BV1_XOR((if _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata then 1bv1 else 0bv1), 1bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 7} {:thread 1} (if _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata ==> BV32_ULT(BV32_UDIV(BV32_MUL(4bv32, _WATCHED_OFFSET), 4bv32), BV32_MUL(BV32_SDIV($j.0, 16bv32), group_size_x)) then 1bv1 else 0bv1) != 0bv1;
    assert {:originated_from_invariant} {:sourceloc_num 8} {:thread 1} (if BV32_SREM($j.0, 16bv32) == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    v0 := BV32_SLT($j.0, $numTimeOffsets);
    goto __partitioned_block_$truebb_0, $falsebb;

  $falsebb:
    assume {:partition} !v0;
    return;

  __partitioned_block_$truebb_0:
    assume {:partition} v0;
    assert {:sourceloc_num 10} {:thread 1} (if BV32_SLT($j.0, 143bv32) then 1bv1 else 0bv1) != 0bv1;
    call _LOG_READ_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata(true, BV32_ADD(BV32_MUL(BV32_ADD(BV32_ADD($j.0, BV32_UDIV(local_id_x$1, 32bv32)), 1bv32), 32bv32), BV32_UREM(local_id_x$1, 32bv32)), $$_ZZ9helloCUDAiifffiiPfS_S_E5sdata[1bv1][BV32_ADD(BV32_MUL(BV32_ADD(BV32_ADD($j.0, BV32_UDIV(local_id_x$1, 32bv32)), 1bv32), 32bv32), BV32_UREM(local_id_x$1, 32bv32))]);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 11} true;
    call _CHECK_READ_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata(true, BV32_ADD(BV32_MUL(BV32_ADD(BV32_ADD($j.0, BV32_UDIV(local_id_x$2, 32bv32)), 1bv32), 32bv32), BV32_UREM(local_id_x$2, 32bv32)), $$_ZZ9helloCUDAiifffiiPfS_S_E5sdata[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(BV32_ADD(BV32_ADD($j.0, BV32_UDIV(local_id_x$2, 32bv32)), 1bv32), 32bv32), BV32_UREM(local_id_x$2, 32bv32))]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata"} true;
    v1$1 := $$_ZZ9helloCUDAiifffiiPfS_S_E5sdata[1bv1][BV32_ADD(BV32_MUL(BV32_ADD(BV32_ADD($j.0, BV32_UDIV(local_id_x$1, 32bv32)), 1bv32), 32bv32), BV32_UREM(local_id_x$1, 32bv32))];
    v1$2 := $$_ZZ9helloCUDAiifffiiPfS_S_E5sdata[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(BV32_ADD(BV32_ADD($j.0, BV32_UDIV(local_id_x$2, 32bv32)), 1bv32), 32bv32), BV32_UREM(local_id_x$2, 32bv32))];
    $$f_j$0bv32$1 := v1$1;
    $$f_j$0bv32$2 := v1$2;
    goto __partitioned_block_$truebb_1;

  __partitioned_block_$truebb_1:
    call $bugle_barrier_duplicated_1(1bv1, 1bv1);
    v2$1 := $$f_j$0bv32$1;
    v2$2 := $$f_j$0bv32$2;
    call _LOG_WRITE_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata(true, BV32_ADD(BV32_MUL(BV32_ADD($j.0, BV32_UDIV(local_id_x$1, 32bv32)), 32bv32), BV32_UREM(local_id_x$1, 32bv32)), v2$1, $$_ZZ9helloCUDAiifffiiPfS_S_E5sdata[1bv1][BV32_ADD(BV32_MUL(BV32_ADD($j.0, BV32_UDIV(local_id_x$1, 32bv32)), 32bv32), BV32_UREM(local_id_x$1, 32bv32))]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata(true, BV32_ADD(BV32_MUL(BV32_ADD($j.0, BV32_UDIV(local_id_x$2, 32bv32)), 32bv32), BV32_UREM(local_id_x$2, 32bv32)));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 15} true;
    call _CHECK_WRITE_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata(true, BV32_ADD(BV32_MUL(BV32_ADD($j.0, BV32_UDIV(local_id_x$2, 32bv32)), 32bv32), BV32_UREM(local_id_x$2, 32bv32)), v2$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata"} true;
    $$_ZZ9helloCUDAiifffiiPfS_S_E5sdata[1bv1][BV32_ADD(BV32_MUL(BV32_ADD($j.0, BV32_UDIV(local_id_x$1, 32bv32)), 32bv32), BV32_UREM(local_id_x$1, 32bv32))] := v2$1;
    $$_ZZ9helloCUDAiifffiiPfS_S_E5sdata[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][BV32_ADD(BV32_MUL(BV32_ADD($j.0, BV32_UDIV(local_id_x$2, 32bv32)), 32bv32), BV32_UREM(local_id_x$2, 32bv32))] := v2$2;
    $j.0 := BV32_ADD($j.0, 16bv32);
    assume {:captureState "loop_back_edge_state_0_0"} true;
    goto $for.cond;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 512bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 1bv32 then 1bv1 else 0bv1) != 0bv1;

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

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_0($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 1bv1;
  modifies $$_ZZ9helloCUDAiifffiiPfS_S_E5sdata, _TRACKING;

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_1($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 1bv1;
  modifies $$_ZZ9helloCUDAiifffiiPfS_S_E5sdata, _TRACKING;

var $$f_j$0bv32$1: bv32;

var $$f_j$0bv32$2: bv32;

const _WATCHED_VALUE_$$volMat: bv32;

procedure {:inline 1} _LOG_READ_$$volMat(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$volMat;

implementation {:inline 1} _LOG_READ_$$volMat(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$volMat := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$volMat == _value then true else _READ_HAS_OCCURRED_$$volMat);
    return;
}

procedure _CHECK_READ_$$volMat(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$volMat && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$volMat);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$volMat && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$volMat: bool;

procedure {:inline 1} _LOG_WRITE_$$volMat(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$volMat, _WRITE_READ_BENIGN_FLAG_$$volMat;

implementation {:inline 1} _LOG_WRITE_$$volMat(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$volMat := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$volMat == _value then true else _WRITE_HAS_OCCURRED_$$volMat);
    _WRITE_READ_BENIGN_FLAG_$$volMat := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$volMat == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$volMat);
    return;
}

procedure _CHECK_WRITE_$$volMat(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$volMat && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$volMat != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$volMat && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$volMat != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$volMat && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$volMat(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$volMat;

implementation {:inline 1} _LOG_ATOMIC_$$volMat(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$volMat := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$volMat);
    return;
}

procedure _CHECK_ATOMIC_$$volMat(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$volMat && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$volMat && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$volMat(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$volMat;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$volMat(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$volMat := (if _P && _WRITE_HAS_OCCURRED_$$volMat && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$volMat);
    return;
}

const _WATCHED_VALUE_$$driftMat: bv32;

procedure {:inline 1} _LOG_READ_$$driftMat(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$driftMat;

implementation {:inline 1} _LOG_READ_$$driftMat(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$driftMat := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$driftMat == _value then true else _READ_HAS_OCCURRED_$$driftMat);
    return;
}

procedure _CHECK_READ_$$driftMat(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$driftMat && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$driftMat);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$driftMat && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$driftMat: bool;

procedure {:inline 1} _LOG_WRITE_$$driftMat(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$driftMat, _WRITE_READ_BENIGN_FLAG_$$driftMat;

implementation {:inline 1} _LOG_WRITE_$$driftMat(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$driftMat := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$driftMat == _value then true else _WRITE_HAS_OCCURRED_$$driftMat);
    _WRITE_READ_BENIGN_FLAG_$$driftMat := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$driftMat == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$driftMat);
    return;
}

procedure _CHECK_WRITE_$$driftMat(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$driftMat && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$driftMat != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$driftMat && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$driftMat != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$driftMat && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$driftMat(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$driftMat;

implementation {:inline 1} _LOG_ATOMIC_$$driftMat(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$driftMat := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$driftMat);
    return;
}

procedure _CHECK_ATOMIC_$$driftMat(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$driftMat && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$driftMat && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$driftMat(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$driftMat;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$driftMat(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$driftMat := (if _P && _WRITE_HAS_OCCURRED_$$driftMat && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$driftMat);
    return;
}

const _WATCHED_VALUE_$$f0: bv32;

procedure {:inline 1} _LOG_READ_$$f0(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$f0;

implementation {:inline 1} _LOG_READ_$$f0(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$f0 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$f0 == _value then true else _READ_HAS_OCCURRED_$$f0);
    return;
}

procedure _CHECK_READ_$$f0(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$f0 && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$f0);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$f0 && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$f0: bool;

procedure {:inline 1} _LOG_WRITE_$$f0(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$f0, _WRITE_READ_BENIGN_FLAG_$$f0;

implementation {:inline 1} _LOG_WRITE_$$f0(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$f0 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$f0 == _value then true else _WRITE_HAS_OCCURRED_$$f0);
    _WRITE_READ_BENIGN_FLAG_$$f0 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$f0 == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$f0);
    return;
}

procedure _CHECK_WRITE_$$f0(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$f0 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$f0 != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$f0 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$f0 != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$f0 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$f0(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$f0;

implementation {:inline 1} _LOG_ATOMIC_$$f0(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$f0 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$f0);
    return;
}

procedure _CHECK_ATOMIC_$$f0(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$f0 && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$f0 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$f0(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$f0;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$f0(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$f0 := (if _P && _WRITE_HAS_OCCURRED_$$f0 && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$f0);
    return;
}

const _WATCHED_VALUE_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata: bv32;

procedure {:inline 1} _LOG_READ_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata;

implementation {:inline 1} _LOG_READ_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata == _value then true else _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata);
    return;
}

procedure _CHECK_READ_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata: bool;

procedure {:inline 1} _LOG_WRITE_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata, _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata;

implementation {:inline 1} _LOG_WRITE_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata == _value then true else _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata);
    _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata);
    return;
}

procedure _CHECK_WRITE_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata;

implementation {:inline 1} _LOG_ATOMIC_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata);
    return;
}

procedure _CHECK_ATOMIC_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata := (if _P && _WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata);
    return;
}

var _TRACKING: bool;

implementation {:inline 1} $bugle_barrier_duplicated_0($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon4_Then, anon4_Else;

  anon4_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata;
    goto anon1;

  anon1:
    goto anon5_Then, anon5_Else;

  anon5_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon3;

  anon3:
    havoc _TRACKING;
    return;

  anon5_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$_ZZ9helloCUDAiifffiiPfS_S_E5sdata;
    goto anon3;

  anon4_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

implementation {:inline 1} $bugle_barrier_duplicated_1($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon4_Then, anon4_Else;

  anon4_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$_ZZ9helloCUDAiifffiiPfS_S_E5sdata;
    goto anon1;

  anon1:
    goto anon5_Then, anon5_Else;

  anon5_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon3;

  anon3:
    havoc _TRACKING;
    return;

  anon5_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$_ZZ9helloCUDAiifffiiPfS_S_E5sdata;
    goto anon3;

  anon4_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;
