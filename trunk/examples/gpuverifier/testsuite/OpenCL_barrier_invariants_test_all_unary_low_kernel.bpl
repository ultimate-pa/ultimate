//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "B"} {:group_shared} $$foo.B: [bv1][bv32]bv32;

axiom {:array_info "$$foo.B"} {:group_shared} {:elem_width 32} {:source_name "B"} {:source_elem_width 32} {:source_dimensions "128"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$foo.B: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$foo.B: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$foo.B: bool;

var {:source_name "C"} {:group_shared} $$foo.C: [bv1][bv32]bv32;

axiom {:array_info "$$foo.C"} {:group_shared} {:elem_width 32} {:source_name "C"} {:source_elem_width 32} {:source_dimensions "128"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$foo.C: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$foo.C: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$foo.C: bool;

var {:source_name "D"} {:group_shared} $$foo.D: [bv1][bv32]bv32;

axiom {:array_info "$$foo.D"} {:group_shared} {:elem_width 32} {:source_name "D"} {:source_elem_width 32} {:source_dimensions "128"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$foo.D: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$foo.D: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$foo.D: bool;

var {:source_name "E"} {:group_shared} $$foo.E: [bv1][bv32]bv32;

axiom {:array_info "$$foo.E"} {:group_shared} {:elem_width 32} {:source_name "E"} {:source_elem_width 32} {:source_dimensions "128"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$foo.E: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$foo.E: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$foo.E: bool;

var {:source_name "F"} {:group_shared} $$foo.F: [bv1][bv32]bv32;

axiom {:array_info "$$foo.F"} {:group_shared} {:elem_width 32} {:source_name "F"} {:source_elem_width 32} {:source_dimensions "128"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$foo.F: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$foo.F: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$foo.F: bool;

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

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvuge"} BV32_UGE(bv32, bv32) : bool;

function {:builtin "bvugt"} BV32_UGT(bv32, bv32) : bool;

function {:builtin "bvule"} BV32_ULE(bv32, bv32) : bool;

function {:builtin "bvult"} BV32_ULT(bv32, bv32) : bool;

procedure {:source_name "foo"} ULTIMATE.start($arbitrary: bv32);
  requires (if BV32_UGE($arbitrary, 0bv32) then 1bv1 else 0bv1) != 0bv1;
  requires (if BV32_ULT($arbitrary, 128bv32) then 1bv1 else 0bv1) != 0bv1;
  requires !_READ_HAS_OCCURRED_$$foo.B && !_WRITE_HAS_OCCURRED_$$foo.B && !_ATOMIC_HAS_OCCURRED_$$foo.B;
  requires !_READ_HAS_OCCURRED_$$foo.C && !_WRITE_HAS_OCCURRED_$$foo.C && !_ATOMIC_HAS_OCCURRED_$$foo.C;
  requires !_READ_HAS_OCCURRED_$$foo.D && !_WRITE_HAS_OCCURRED_$$foo.D && !_ATOMIC_HAS_OCCURRED_$$foo.D;
  requires !_READ_HAS_OCCURRED_$$foo.E && !_WRITE_HAS_OCCURRED_$$foo.E && !_ATOMIC_HAS_OCCURRED_$$foo.E;
  requires !_READ_HAS_OCCURRED_$$foo.F && !_WRITE_HAS_OCCURRED_$$foo.F && !_ATOMIC_HAS_OCCURRED_$$foo.F;
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
  modifies $$foo.B, $$foo.C, $$foo.D, $$foo.E, $$foo.F, _WRITE_HAS_OCCURRED_$$foo.B, _WRITE_READ_BENIGN_FLAG_$$foo.B, _WRITE_READ_BENIGN_FLAG_$$foo.B, _WRITE_HAS_OCCURRED_$$foo.C, _WRITE_READ_BENIGN_FLAG_$$foo.C, _WRITE_READ_BENIGN_FLAG_$$foo.C, _WRITE_HAS_OCCURRED_$$foo.D, _WRITE_READ_BENIGN_FLAG_$$foo.D, _WRITE_READ_BENIGN_FLAG_$$foo.D, _WRITE_HAS_OCCURRED_$$foo.E, _WRITE_READ_BENIGN_FLAG_$$foo.E, _WRITE_READ_BENIGN_FLAG_$$foo.E, _WRITE_HAS_OCCURRED_$$foo.F, _WRITE_READ_BENIGN_FLAG_$$foo.F, _WRITE_READ_BENIGN_FLAG_$$foo.F, _NOT_ACCESSED_$$foo.B, _NOT_ACCESSED_$$foo.C, _NOT_ACCESSED_$$foo.D, _NOT_ACCESSED_$$foo.E, _NOT_ACCESSED_$$foo.F, _TRACKING, _READ_HAS_OCCURRED_$$foo.B, _READ_HAS_OCCURRED_$$foo.C, _READ_HAS_OCCURRED_$$foo.D, _READ_HAS_OCCURRED_$$foo.E, _READ_HAS_OCCURRED_$$foo.F;

implementation {:source_name "foo"} ULTIMATE.start($arbitrary: bv32)
{
  var $0$1: bv1;
  var $0$2: bv1;
  var $1$1: bv1;
  var $1$2: bv1;
  var $2$1: bv1;
  var $2$2: bv1;
  var $3$1: bv1;
  var $3$2: bv1;
  var $4$1: bv1;
  var $4$2: bv1;
  var v0: bool;
  var v1$1: bv32;
  var v1$2: bv32;
  var v2$1: bv32;
  var v2$2: bv32;
  var v3: bool;
  var v4$1: bv32;
  var v4$2: bv32;
  var v5$1: bv32;
  var v5$2: bv32;
  var v6: bool;
  var v7$1: bv32;
  var v7$2: bv32;
  var v8$1: bv32;
  var v8$2: bv32;
  var v9: bool;
  var v10$1: bv32;
  var v10$2: bv32;
  var v11$1: bv32;
  var v11$2: bv32;
  var v12: bool;
  var v13$1: bv32;
  var v13$2: bv32;
  var v14$1: bv32;
  var v14$2: bv32;

  __partitioned_block_$entry_0:
    call _LOG_WRITE_$$foo.B(true, local_id_x$1, local_id_x$1, $$foo.B[1bv1][local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.B(true, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 3} true;
    call _CHECK_WRITE_$$foo.B(true, local_id_x$2, local_id_x$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$foo.B"} true;
    $$foo.B[1bv1][local_id_x$1] := local_id_x$1;
    $$foo.B[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] := local_id_x$2;
    assume _NOT_ACCESSED_$$foo.B != local_id_x$1 && _NOT_ACCESSED_$$foo.B != local_id_x$2;
    call _LOG_WRITE_$$foo.C(true, local_id_x$1, local_id_x$1, $$foo.C[1bv1][local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.C(true, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 4} true;
    call _CHECK_WRITE_$$foo.C(true, local_id_x$2, local_id_x$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$foo.C"} true;
    $$foo.C[1bv1][local_id_x$1] := local_id_x$1;
    $$foo.C[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] := local_id_x$2;
    assume _NOT_ACCESSED_$$foo.C != local_id_x$1 && _NOT_ACCESSED_$$foo.C != local_id_x$2;
    call _LOG_WRITE_$$foo.D(true, local_id_x$1, local_id_x$1, $$foo.D[1bv1][local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.D(true, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 5} true;
    call _CHECK_WRITE_$$foo.D(true, local_id_x$2, local_id_x$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$foo.D"} true;
    $$foo.D[1bv1][local_id_x$1] := local_id_x$1;
    $$foo.D[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] := local_id_x$2;
    assume _NOT_ACCESSED_$$foo.D != local_id_x$1 && _NOT_ACCESSED_$$foo.D != local_id_x$2;
    call _LOG_WRITE_$$foo.E(true, local_id_x$1, local_id_x$1, $$foo.E[1bv1][local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.E(true, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 6} true;
    call _CHECK_WRITE_$$foo.E(true, local_id_x$2, local_id_x$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$foo.E"} true;
    $$foo.E[1bv1][local_id_x$1] := local_id_x$1;
    $$foo.E[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] := local_id_x$2;
    assume _NOT_ACCESSED_$$foo.E != local_id_x$1 && _NOT_ACCESSED_$$foo.E != local_id_x$2;
    call _LOG_WRITE_$$foo.F(true, local_id_x$1, local_id_x$1, $$foo.F[1bv1][local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.F(true, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_4"} {:captureState "check_state_4"} {:sourceloc} {:sourceloc_num 7} true;
    call _CHECK_WRITE_$$foo.F(true, local_id_x$2, local_id_x$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$foo.F"} true;
    $$foo.F[1bv1][local_id_x$1] := local_id_x$1;
    $$foo.F[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] := local_id_x$2;
    assume _NOT_ACCESSED_$$foo.F != local_id_x$1 && _NOT_ACCESSED_$$foo.F != local_id_x$2;
    assert {:barrier_invariant true} {:sourceloc_num 8} {:thread 1} true ==> (if $$foo.B[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assert {:barrier_invariant_access_check true} {:sourceloc_num 8} {:thread 1} true ==> true ==> _NOT_ACCESSED_$$foo.B != local_id_x$1;
    assert {:barrier_invariant true} {:sourceloc_num 9} {:thread 1} true ==> (if $$foo.C[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assert {:barrier_invariant_access_check true} {:sourceloc_num 9} {:thread 1} true ==> true ==> _NOT_ACCESSED_$$foo.C != local_id_x$1;
    assert {:barrier_invariant true} {:sourceloc_num 10} {:thread 1} true ==> (if $$foo.D[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assert {:barrier_invariant_access_check true} {:sourceloc_num 10} {:thread 1} true ==> true ==> _NOT_ACCESSED_$$foo.D != local_id_x$1;
    assert {:barrier_invariant true} {:sourceloc_num 11} {:thread 1} true ==> (if $$foo.E[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assert {:barrier_invariant_access_check true} {:sourceloc_num 11} {:thread 1} true ==> true ==> _NOT_ACCESSED_$$foo.E != local_id_x$1;
    assert {:barrier_invariant true} {:sourceloc_num 12} {:thread 1} true ==> (if $$foo.F[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assert {:barrier_invariant_access_check true} {:sourceloc_num 12} {:thread 1} true ==> true ==> _NOT_ACCESSED_$$foo.F != local_id_x$1;
    goto __partitioned_block_$entry_1;

  __partitioned_block_$entry_1:
    call $bugle_barrier_duplicated_0(1bv1, 0bv1);
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.B[1bv1][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.B[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.B[1bv1][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.B[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$1, 0bv32) && BV32_SLT(local_id_x$1, group_size_x) ==> (if $$foo.B[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$2, 0bv32) && BV32_SLT(local_id_x$2, group_size_x) ==> (if $$foo.B[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] == local_id_x$2 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.C[1bv1][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.C[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.C[1bv1][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.C[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(2bv32, 0bv32) && BV32_SLT(2bv32, group_size_x) ==> (if $$foo.C[1bv1][2bv32] == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(2bv32, 0bv32) && BV32_SLT(2bv32, group_size_x) ==> (if $$foo.C[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][2bv32] == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(3bv32, 0bv32) && BV32_SLT(3bv32, group_size_x) ==> (if $$foo.C[1bv1][3bv32] == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(3bv32, 0bv32) && BV32_SLT(3bv32, group_size_x) ==> (if $$foo.C[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][3bv32] == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$1, 0bv32) && BV32_SLT(local_id_x$1, group_size_x) ==> (if $$foo.C[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$2, 0bv32) && BV32_SLT(local_id_x$2, group_size_x) ==> (if $$foo.C[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] == local_id_x$2 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.D[1bv1][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.D[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.D[1bv1][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.D[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(2bv32, 0bv32) && BV32_SLT(2bv32, group_size_x) ==> (if $$foo.D[1bv1][2bv32] == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(2bv32, 0bv32) && BV32_SLT(2bv32, group_size_x) ==> (if $$foo.D[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][2bv32] == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(3bv32, 0bv32) && BV32_SLT(3bv32, group_size_x) ==> (if $$foo.D[1bv1][3bv32] == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(3bv32, 0bv32) && BV32_SLT(3bv32, group_size_x) ==> (if $$foo.D[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][3bv32] == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(4bv32, 0bv32) && BV32_SLT(4bv32, group_size_x) ==> (if $$foo.D[1bv1][4bv32] == 4bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(4bv32, 0bv32) && BV32_SLT(4bv32, group_size_x) ==> (if $$foo.D[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][4bv32] == 4bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(5bv32, 0bv32) && BV32_SLT(5bv32, group_size_x) ==> (if $$foo.D[1bv1][5bv32] == 5bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(5bv32, 0bv32) && BV32_SLT(5bv32, group_size_x) ==> (if $$foo.D[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][5bv32] == 5bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$1, 0bv32) && BV32_SLT(local_id_x$1, group_size_x) ==> (if $$foo.D[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$2, 0bv32) && BV32_SLT(local_id_x$2, group_size_x) ==> (if $$foo.D[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] == local_id_x$2 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.E[1bv1][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.E[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.E[1bv1][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.E[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(2bv32, 0bv32) && BV32_SLT(2bv32, group_size_x) ==> (if $$foo.E[1bv1][2bv32] == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(2bv32, 0bv32) && BV32_SLT(2bv32, group_size_x) ==> (if $$foo.E[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][2bv32] == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(3bv32, 0bv32) && BV32_SLT(3bv32, group_size_x) ==> (if $$foo.E[1bv1][3bv32] == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(3bv32, 0bv32) && BV32_SLT(3bv32, group_size_x) ==> (if $$foo.E[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][3bv32] == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(4bv32, 0bv32) && BV32_SLT(4bv32, group_size_x) ==> (if $$foo.E[1bv1][4bv32] == 4bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(4bv32, 0bv32) && BV32_SLT(4bv32, group_size_x) ==> (if $$foo.E[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][4bv32] == 4bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(5bv32, 0bv32) && BV32_SLT(5bv32, group_size_x) ==> (if $$foo.E[1bv1][5bv32] == 5bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(5bv32, 0bv32) && BV32_SLT(5bv32, group_size_x) ==> (if $$foo.E[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][5bv32] == 5bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(6bv32, 0bv32) && BV32_SLT(6bv32, group_size_x) ==> (if $$foo.E[1bv1][6bv32] == 6bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(6bv32, 0bv32) && BV32_SLT(6bv32, group_size_x) ==> (if $$foo.E[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][6bv32] == 6bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(7bv32, 0bv32) && BV32_SLT(7bv32, group_size_x) ==> (if $$foo.E[1bv1][7bv32] == 7bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(7bv32, 0bv32) && BV32_SLT(7bv32, group_size_x) ==> (if $$foo.E[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][7bv32] == 7bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$1, 0bv32) && BV32_SLT(local_id_x$1, group_size_x) ==> (if $$foo.E[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$2, 0bv32) && BV32_SLT(local_id_x$2, group_size_x) ==> (if $$foo.E[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] == local_id_x$2 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.F[1bv1][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.F[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.F[1bv1][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.F[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(2bv32, 0bv32) && BV32_SLT(2bv32, group_size_x) ==> (if $$foo.F[1bv1][2bv32] == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(2bv32, 0bv32) && BV32_SLT(2bv32, group_size_x) ==> (if $$foo.F[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][2bv32] == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(3bv32, 0bv32) && BV32_SLT(3bv32, group_size_x) ==> (if $$foo.F[1bv1][3bv32] == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(3bv32, 0bv32) && BV32_SLT(3bv32, group_size_x) ==> (if $$foo.F[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][3bv32] == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(4bv32, 0bv32) && BV32_SLT(4bv32, group_size_x) ==> (if $$foo.F[1bv1][4bv32] == 4bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(4bv32, 0bv32) && BV32_SLT(4bv32, group_size_x) ==> (if $$foo.F[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][4bv32] == 4bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(5bv32, 0bv32) && BV32_SLT(5bv32, group_size_x) ==> (if $$foo.F[1bv1][5bv32] == 5bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(5bv32, 0bv32) && BV32_SLT(5bv32, group_size_x) ==> (if $$foo.F[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][5bv32] == 5bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(6bv32, 0bv32) && BV32_SLT(6bv32, group_size_x) ==> (if $$foo.F[1bv1][6bv32] == 6bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(6bv32, 0bv32) && BV32_SLT(6bv32, group_size_x) ==> (if $$foo.F[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][6bv32] == 6bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(7bv32, 0bv32) && BV32_SLT(7bv32, group_size_x) ==> (if $$foo.F[1bv1][7bv32] == 7bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(7bv32, 0bv32) && BV32_SLT(7bv32, group_size_x) ==> (if $$foo.F[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][7bv32] == 7bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(8bv32, 0bv32) && BV32_SLT(8bv32, group_size_x) ==> (if $$foo.F[1bv1][8bv32] == 8bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(8bv32, 0bv32) && BV32_SLT(8bv32, group_size_x) ==> (if $$foo.F[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][8bv32] == 8bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(9bv32, 0bv32) && BV32_SLT(9bv32, group_size_x) ==> (if $$foo.F[1bv1][9bv32] == 9bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(9bv32, 0bv32) && BV32_SLT(9bv32, group_size_x) ==> (if $$foo.F[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][9bv32] == 9bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$1, 0bv32) && BV32_SLT(local_id_x$1, group_size_x) ==> (if $$foo.F[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$2, 0bv32) && BV32_SLT(local_id_x$2, group_size_x) ==> (if $$foo.F[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] == local_id_x$2 then 1bv1 else 0bv1) != 0bv1;
    v0 := BV32_ULE($arbitrary, 1bv32);
    goto $truebb, $falsebb;

  $falsebb:
    assume {:partition} !v0;
    $0$1 := 0bv1;
    $0$2 := 0bv1;
    goto $land.end;

  $land.end:
    assume {:do_not_predicate} {:check_id "check_state_5"} {:captureState "check_state_5"} {:sourceloc} {:sourceloc_num 16} true;
    v1$1 := $$foo.B[1bv1][local_id_x$1];
    v1$2 := $$foo.B[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2];
    assume _NOT_ACCESSED_$$foo.B != local_id_x$1 && _NOT_ACCESSED_$$foo.B != local_id_x$2;
    assume {:do_not_predicate} {:check_id "check_state_6"} {:captureState "check_state_6"} {:sourceloc} {:sourceloc_num 17} true;
    v2$1 := $$foo.B[1bv1][$arbitrary];
    v2$2 := $$foo.B[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][$arbitrary];
    assume _NOT_ACCESSED_$$foo.B != $arbitrary && _NOT_ACCESSED_$$foo.B != $arbitrary;
    assert {:sourceloc_num 18} {:thread 1} (if $0$1 == 1bv1 ==> BV32_SGT(v1$1, v2$1) then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 18} {:thread 2} (if $0$2 == 1bv1 ==> BV32_SGT(v1$2, v2$2) then 1bv1 else 0bv1) != 0bv1;
    v3 := BV32_ULE($arbitrary, 3bv32);
    goto $truebb0, $falsebb0;

  $falsebb0:
    assume {:partition} !v3;
    $1$1 := 0bv1;
    $1$2 := 0bv1;
    goto $land.end52;

  $land.end52:
    assume {:do_not_predicate} {:check_id "check_state_7"} {:captureState "check_state_7"} {:sourceloc} {:sourceloc_num 21} true;
    v4$1 := $$foo.C[1bv1][local_id_x$1];
    v4$2 := $$foo.C[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2];
    assume _NOT_ACCESSED_$$foo.C != local_id_x$1 && _NOT_ACCESSED_$$foo.C != local_id_x$2;
    assume {:do_not_predicate} {:check_id "check_state_8"} {:captureState "check_state_8"} {:sourceloc} {:sourceloc_num 22} true;
    v5$1 := $$foo.C[1bv1][$arbitrary];
    v5$2 := $$foo.C[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][$arbitrary];
    assume _NOT_ACCESSED_$$foo.C != $arbitrary && _NOT_ACCESSED_$$foo.C != $arbitrary;
    assert {:sourceloc_num 23} {:thread 1} (if $1$1 == 1bv1 ==> BV32_SGT(v4$1, v5$1) then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 23} {:thread 2} (if $1$2 == 1bv1 ==> BV32_SGT(v4$2, v5$2) then 1bv1 else 0bv1) != 0bv1;
    v6 := BV32_ULE($arbitrary, 5bv32);
    goto $truebb1, $falsebb1;

  $falsebb1:
    assume {:partition} !v6;
    $2$1 := 0bv1;
    $2$2 := 0bv1;
    goto $land.end62;

  $land.end62:
    assume {:do_not_predicate} {:check_id "check_state_9"} {:captureState "check_state_9"} {:sourceloc} {:sourceloc_num 26} true;
    v7$1 := $$foo.D[1bv1][local_id_x$1];
    v7$2 := $$foo.D[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2];
    assume _NOT_ACCESSED_$$foo.D != local_id_x$1 && _NOT_ACCESSED_$$foo.D != local_id_x$2;
    assume {:do_not_predicate} {:check_id "check_state_10"} {:captureState "check_state_10"} {:sourceloc} {:sourceloc_num 27} true;
    v8$1 := $$foo.D[1bv1][$arbitrary];
    v8$2 := $$foo.D[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][$arbitrary];
    assume _NOT_ACCESSED_$$foo.D != $arbitrary && _NOT_ACCESSED_$$foo.D != $arbitrary;
    assert {:sourceloc_num 28} {:thread 1} (if $2$1 == 1bv1 ==> BV32_SGT(v7$1, v8$1) then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 28} {:thread 2} (if $2$2 == 1bv1 ==> BV32_SGT(v7$2, v8$2) then 1bv1 else 0bv1) != 0bv1;
    v9 := BV32_ULE($arbitrary, 7bv32);
    goto $truebb2, $falsebb2;

  $falsebb2:
    assume {:partition} !v9;
    $3$1 := 0bv1;
    $3$2 := 0bv1;
    goto $land.end72;

  $land.end72:
    assume {:do_not_predicate} {:check_id "check_state_11"} {:captureState "check_state_11"} {:sourceloc} {:sourceloc_num 31} true;
    v10$1 := $$foo.E[1bv1][local_id_x$1];
    v10$2 := $$foo.E[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2];
    assume _NOT_ACCESSED_$$foo.E != local_id_x$1 && _NOT_ACCESSED_$$foo.E != local_id_x$2;
    assume {:do_not_predicate} {:check_id "check_state_12"} {:captureState "check_state_12"} {:sourceloc} {:sourceloc_num 32} true;
    v11$1 := $$foo.E[1bv1][$arbitrary];
    v11$2 := $$foo.E[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][$arbitrary];
    assume _NOT_ACCESSED_$$foo.E != $arbitrary && _NOT_ACCESSED_$$foo.E != $arbitrary;
    assert {:sourceloc_num 33} {:thread 1} (if $3$1 == 1bv1 ==> BV32_SGT(v10$1, v11$1) then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 33} {:thread 2} (if $3$2 == 1bv1 ==> BV32_SGT(v10$2, v11$2) then 1bv1 else 0bv1) != 0bv1;
    v12 := BV32_ULE($arbitrary, 9bv32);
    goto $truebb3, $falsebb3;

  $falsebb3:
    assume {:partition} !v12;
    $4$1 := 0bv1;
    $4$2 := 0bv1;
    goto $land.end82;

  $land.end82:
    assume {:do_not_predicate} {:check_id "check_state_13"} {:captureState "check_state_13"} {:sourceloc} {:sourceloc_num 36} true;
    v13$1 := $$foo.F[1bv1][local_id_x$1];
    v13$2 := $$foo.F[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2];
    assume _NOT_ACCESSED_$$foo.F != local_id_x$1 && _NOT_ACCESSED_$$foo.F != local_id_x$2;
    assume {:do_not_predicate} {:check_id "check_state_14"} {:captureState "check_state_14"} {:sourceloc} {:sourceloc_num 37} true;
    v14$1 := $$foo.F[1bv1][$arbitrary];
    v14$2 := $$foo.F[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][$arbitrary];
    assume _NOT_ACCESSED_$$foo.F != $arbitrary && _NOT_ACCESSED_$$foo.F != $arbitrary;
    assert {:sourceloc_num 38} {:thread 1} (if $4$1 == 1bv1 ==> BV32_SGT(v13$1, v14$1) then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 38} {:thread 2} (if $4$2 == 1bv1 ==> BV32_SGT(v13$2, v14$2) then 1bv1 else 0bv1) != 0bv1;
    return;

  $truebb3:
    assume {:partition} v12;
    $4$1 := (if BV32_UGT(local_id_x$1, $arbitrary) then 1bv1 else 0bv1);
    $4$2 := (if BV32_UGT(local_id_x$2, $arbitrary) then 1bv1 else 0bv1);
    goto $land.end82;

  $truebb2:
    assume {:partition} v9;
    $3$1 := (if BV32_UGT(local_id_x$1, $arbitrary) then 1bv1 else 0bv1);
    $3$2 := (if BV32_UGT(local_id_x$2, $arbitrary) then 1bv1 else 0bv1);
    goto $land.end72;

  $truebb1:
    assume {:partition} v6;
    $2$1 := (if BV32_UGT(local_id_x$1, $arbitrary) then 1bv1 else 0bv1);
    $2$2 := (if BV32_UGT(local_id_x$2, $arbitrary) then 1bv1 else 0bv1);
    goto $land.end62;

  $truebb0:
    assume {:partition} v3;
    $1$1 := (if BV32_UGT(local_id_x$1, $arbitrary) then 1bv1 else 0bv1);
    $1$2 := (if BV32_UGT(local_id_x$2, $arbitrary) then 1bv1 else 0bv1);
    goto $land.end52;

  $truebb:
    assume {:partition} v0;
    $0$1 := (if BV32_UGT(local_id_x$1, $arbitrary) then 1bv1 else 0bv1);
    $0$2 := (if BV32_UGT(local_id_x$2, $arbitrary) then 1bv1 else 0bv1);
    goto $land.end;
}

procedure {:source_name "__barrier_invariant_3"} {:barrier_invariant} $__barrier_invariant_33($instantiation1: bv32, $instantiation2: bv32, $expr$1: bv1, $instantiation3$1: bv32, $expr$2: bv1, $instantiation3$2: bv32);
  requires $instantiation1 == 0bv32;
  requires $instantiation2 == 1bv32;

procedure {:source_name "__barrier_invariant_5"} {:barrier_invariant} $__barrier_invariant_55($instantiation1: bv32, $instantiation2: bv32, $instantiation3: bv32, $instantiation4: bv32, $expr$1: bv1, $instantiation5$1: bv32, $expr$2: bv1, $instantiation5$2: bv32);
  requires $instantiation1 == 0bv32;
  requires $instantiation2 == 1bv32;
  requires $instantiation3 == 2bv32;
  requires $instantiation4 == 3bv32;

procedure {:source_name "__barrier_invariant_7"} {:barrier_invariant} $__barrier_invariant_77($instantiation1: bv32, $instantiation2: bv32, $instantiation3: bv32, $instantiation4: bv32, $instantiation5: bv32, $instantiation6: bv32, $expr$1: bv1, $instantiation7$1: bv32, $expr$2: bv1, $instantiation7$2: bv32);
  requires $instantiation1 == 0bv32;
  requires $instantiation2 == 1bv32;
  requires $instantiation3 == 2bv32;
  requires $instantiation4 == 3bv32;
  requires $instantiation5 == 4bv32;
  requires $instantiation6 == 5bv32;

procedure {:source_name "__barrier_invariant_9"} {:barrier_invariant} $__barrier_invariant_99($instantiation1: bv32, $instantiation2: bv32, $instantiation3: bv32, $instantiation4: bv32, $instantiation5: bv32, $instantiation6: bv32, $instantiation7: bv32, $instantiation8: bv32, $expr$1: bv1, $instantiation9$1: bv32, $expr$2: bv1, $instantiation9$2: bv32);
  requires $instantiation1 == 0bv32;
  requires $instantiation2 == 1bv32;
  requires $instantiation3 == 2bv32;
  requires $instantiation4 == 3bv32;
  requires $instantiation5 == 4bv32;
  requires $instantiation6 == 5bv32;
  requires $instantiation7 == 6bv32;
  requires $instantiation8 == 7bv32;

procedure {:source_name "__barrier_invariant_11"} {:barrier_invariant} $__barrier_invariant_1111($instantiation1: bv32, $instantiation2: bv32, $instantiation3: bv32, $instantiation4: bv32, $instantiation5: bv32, $instantiation6: bv32, $instantiation7: bv32, $instantiation8: bv32, $instantiation9: bv32, $instantiation10: bv32, $expr$1: bv1, $instantiation11$1: bv32, $expr$2: bv1, $instantiation11$2: bv32);
  requires $instantiation1 == 0bv32;
  requires $instantiation2 == 1bv32;
  requires $instantiation3 == 2bv32;
  requires $instantiation4 == 3bv32;
  requires $instantiation5 == 4bv32;
  requires $instantiation6 == 5bv32;
  requires $instantiation7 == 6bv32;
  requires $instantiation8 == 7bv32;
  requires $instantiation9 == 8bv32;
  requires $instantiation10 == 9bv32;

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 128bv32 then 1bv1 else 0bv1) != 0bv1;

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

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_0($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 0bv1;
  modifies $$foo.B, $$foo.C, $$foo.D, $$foo.E, $$foo.F, _NOT_ACCESSED_$$foo.B, _NOT_ACCESSED_$$foo.C, _NOT_ACCESSED_$$foo.D, _NOT_ACCESSED_$$foo.E, _NOT_ACCESSED_$$foo.F, _TRACKING;

var {:check_access} _NOT_ACCESSED_$$foo.B: bv32;

var {:check_access} _NOT_ACCESSED_$$foo.C: bv32;

var {:check_access} _NOT_ACCESSED_$$foo.D: bv32;

var {:check_access} _NOT_ACCESSED_$$foo.E: bv32;

var {:check_access} _NOT_ACCESSED_$$foo.F: bv32;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;

const _WATCHED_VALUE_$$foo.B: bv32;

procedure {:inline 1} _LOG_READ_$$foo.B(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$foo.B;

implementation {:inline 1} _LOG_READ_$$foo.B(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$foo.B := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.B == _value then true else _READ_HAS_OCCURRED_$$foo.B);
    return;
}

procedure _CHECK_READ_$$foo.B(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.B && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$foo.B && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.B && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$foo.B: bool;

procedure {:inline 1} _LOG_WRITE_$$foo.B(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$foo.B, _WRITE_READ_BENIGN_FLAG_$$foo.B;

implementation {:inline 1} _LOG_WRITE_$$foo.B(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$foo.B := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.B == _value then true else _WRITE_HAS_OCCURRED_$$foo.B);
    _WRITE_READ_BENIGN_FLAG_$$foo.B := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.B == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$foo.B);
    return;
}

procedure _CHECK_WRITE_$$foo.B(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.B && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.B != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.B && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.B != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.B && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$foo.B(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$foo.B;

implementation {:inline 1} _LOG_ATOMIC_$$foo.B(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$foo.B := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$foo.B);
    return;
}

procedure _CHECK_ATOMIC_$$foo.B(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.B && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.B && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.B(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$foo.B;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.B(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$foo.B := (if _P && _WRITE_HAS_OCCURRED_$$foo.B && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$foo.B);
    return;
}

const _WATCHED_VALUE_$$foo.C: bv32;

procedure {:inline 1} _LOG_READ_$$foo.C(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$foo.C;

implementation {:inline 1} _LOG_READ_$$foo.C(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$foo.C := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.C == _value then true else _READ_HAS_OCCURRED_$$foo.C);
    return;
}

procedure _CHECK_READ_$$foo.C(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.C && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$foo.C && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.C && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$foo.C: bool;

procedure {:inline 1} _LOG_WRITE_$$foo.C(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$foo.C, _WRITE_READ_BENIGN_FLAG_$$foo.C;

implementation {:inline 1} _LOG_WRITE_$$foo.C(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$foo.C := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.C == _value then true else _WRITE_HAS_OCCURRED_$$foo.C);
    _WRITE_READ_BENIGN_FLAG_$$foo.C := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.C == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$foo.C);
    return;
}

procedure _CHECK_WRITE_$$foo.C(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.C && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.C != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.C && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.C != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.C && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$foo.C(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$foo.C;

implementation {:inline 1} _LOG_ATOMIC_$$foo.C(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$foo.C := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$foo.C);
    return;
}

procedure _CHECK_ATOMIC_$$foo.C(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.C && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.C && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.C(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$foo.C;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.C(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$foo.C := (if _P && _WRITE_HAS_OCCURRED_$$foo.C && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$foo.C);
    return;
}

const _WATCHED_VALUE_$$foo.D: bv32;

procedure {:inline 1} _LOG_READ_$$foo.D(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$foo.D;

implementation {:inline 1} _LOG_READ_$$foo.D(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$foo.D := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.D == _value then true else _READ_HAS_OCCURRED_$$foo.D);
    return;
}

procedure _CHECK_READ_$$foo.D(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.D && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$foo.D && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.D && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$foo.D: bool;

procedure {:inline 1} _LOG_WRITE_$$foo.D(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$foo.D, _WRITE_READ_BENIGN_FLAG_$$foo.D;

implementation {:inline 1} _LOG_WRITE_$$foo.D(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$foo.D := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.D == _value then true else _WRITE_HAS_OCCURRED_$$foo.D);
    _WRITE_READ_BENIGN_FLAG_$$foo.D := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.D == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$foo.D);
    return;
}

procedure _CHECK_WRITE_$$foo.D(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.D && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.D != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.D && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.D != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.D && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$foo.D(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$foo.D;

implementation {:inline 1} _LOG_ATOMIC_$$foo.D(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$foo.D := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$foo.D);
    return;
}

procedure _CHECK_ATOMIC_$$foo.D(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.D && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.D && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.D(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$foo.D;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.D(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$foo.D := (if _P && _WRITE_HAS_OCCURRED_$$foo.D && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$foo.D);
    return;
}

const _WATCHED_VALUE_$$foo.E: bv32;

procedure {:inline 1} _LOG_READ_$$foo.E(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$foo.E;

implementation {:inline 1} _LOG_READ_$$foo.E(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$foo.E := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.E == _value then true else _READ_HAS_OCCURRED_$$foo.E);
    return;
}

procedure _CHECK_READ_$$foo.E(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.E && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$foo.E && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.E && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$foo.E: bool;

procedure {:inline 1} _LOG_WRITE_$$foo.E(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$foo.E, _WRITE_READ_BENIGN_FLAG_$$foo.E;

implementation {:inline 1} _LOG_WRITE_$$foo.E(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$foo.E := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.E == _value then true else _WRITE_HAS_OCCURRED_$$foo.E);
    _WRITE_READ_BENIGN_FLAG_$$foo.E := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.E == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$foo.E);
    return;
}

procedure _CHECK_WRITE_$$foo.E(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.E && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.E != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.E && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.E != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.E && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$foo.E(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$foo.E;

implementation {:inline 1} _LOG_ATOMIC_$$foo.E(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$foo.E := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$foo.E);
    return;
}

procedure _CHECK_ATOMIC_$$foo.E(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.E && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.E && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.E(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$foo.E;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.E(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$foo.E := (if _P && _WRITE_HAS_OCCURRED_$$foo.E && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$foo.E);
    return;
}

const _WATCHED_VALUE_$$foo.F: bv32;

procedure {:inline 1} _LOG_READ_$$foo.F(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$foo.F;

implementation {:inline 1} _LOG_READ_$$foo.F(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$foo.F := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.F == _value then true else _READ_HAS_OCCURRED_$$foo.F);
    return;
}

procedure _CHECK_READ_$$foo.F(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.F && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$foo.F && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.F && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$foo.F: bool;

procedure {:inline 1} _LOG_WRITE_$$foo.F(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$foo.F, _WRITE_READ_BENIGN_FLAG_$$foo.F;

implementation {:inline 1} _LOG_WRITE_$$foo.F(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$foo.F := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.F == _value then true else _WRITE_HAS_OCCURRED_$$foo.F);
    _WRITE_READ_BENIGN_FLAG_$$foo.F := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.F == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$foo.F);
    return;
}

procedure _CHECK_WRITE_$$foo.F(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.F && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.F != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.F && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.F != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.F && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$foo.F(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$foo.F;

implementation {:inline 1} _LOG_ATOMIC_$$foo.F(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$foo.F := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$foo.F);
    return;
}

procedure _CHECK_ATOMIC_$$foo.F(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.F && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.F && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.F(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$foo.F;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.F(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$foo.F := (if _P && _WRITE_HAS_OCCURRED_$$foo.F && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$foo.F);
    return;
}

var _TRACKING: bool;

implementation {:inline 1} $bugle_barrier_duplicated_0($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon17_Then, anon17_Else;

  anon17_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$foo.B;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$foo.B;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$foo.B;
    goto anon1;

  anon1:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$foo.C;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$foo.C;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$foo.C;
    goto anon2;

  anon2:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$foo.D;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$foo.D;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$foo.D;
    goto anon3;

  anon3:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$foo.E;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$foo.E;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$foo.E;
    goto anon4;

  anon4:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$foo.F;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$foo.F;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$foo.F;
    goto anon5;

  anon5:
    goto anon18_Then, anon18_Else;

  anon18_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon16;

  anon16:
    havoc _TRACKING;
    return;

  anon18_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$foo.B;
    goto anon7;

  anon7:
    havoc $$foo.C;
    goto anon8;

  anon8:
    havoc $$foo.D;
    goto anon9;

  anon9:
    havoc $$foo.E;
    goto anon10;

  anon10:
    havoc $$foo.F;
    goto anon11;

  anon11:
    havoc _NOT_ACCESSED_$$foo.B;
    goto anon12;

  anon12:
    havoc _NOT_ACCESSED_$$foo.C;
    goto anon13;

  anon13:
    havoc _NOT_ACCESSED_$$foo.D;
    goto anon14;

  anon14:
    havoc _NOT_ACCESSED_$$foo.E;
    goto anon15;

  anon15:
    havoc _NOT_ACCESSED_$$foo.F;
    goto anon16;

  anon17_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

