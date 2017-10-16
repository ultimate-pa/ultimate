//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "G"} {:group_shared} $$foo.G: [bv1][bv32]bv32;

axiom {:array_info "$$foo.G"} {:group_shared} {:elem_width 32} {:source_name "G"} {:source_elem_width 32} {:source_dimensions "128"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$foo.G: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$foo.G: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$foo.G: bool;

var {:source_name "H"} {:group_shared} $$foo.H: [bv1][bv32]bv32;

axiom {:array_info "$$foo.H"} {:group_shared} {:elem_width 32} {:source_name "H"} {:source_elem_width 32} {:source_dimensions "128"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$foo.H: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$foo.H: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$foo.H: bool;

var {:source_name "I"} {:group_shared} $$foo.I: [bv1][bv32]bv32;

axiom {:array_info "$$foo.I"} {:group_shared} {:elem_width 32} {:source_name "I"} {:source_elem_width 32} {:source_dimensions "128"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$foo.I: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$foo.I: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$foo.I: bool;

var {:source_name "J"} {:group_shared} $$foo.J: [bv1][bv32]bv32;

axiom {:array_info "$$foo.J"} {:group_shared} {:elem_width 32} {:source_name "J"} {:source_elem_width 32} {:source_dimensions "128"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$foo.J: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$foo.J: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$foo.J: bool;

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
  requires !_READ_HAS_OCCURRED_$$foo.G && !_WRITE_HAS_OCCURRED_$$foo.G && !_ATOMIC_HAS_OCCURRED_$$foo.G;
  requires !_READ_HAS_OCCURRED_$$foo.H && !_WRITE_HAS_OCCURRED_$$foo.H && !_ATOMIC_HAS_OCCURRED_$$foo.H;
  requires !_READ_HAS_OCCURRED_$$foo.I && !_WRITE_HAS_OCCURRED_$$foo.I && !_ATOMIC_HAS_OCCURRED_$$foo.I;
  requires !_READ_HAS_OCCURRED_$$foo.J && !_WRITE_HAS_OCCURRED_$$foo.J && !_ATOMIC_HAS_OCCURRED_$$foo.J;
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
  modifies $$foo.G, $$foo.H, $$foo.I, $$foo.J, _WRITE_HAS_OCCURRED_$$foo.G, _WRITE_READ_BENIGN_FLAG_$$foo.G, _WRITE_READ_BENIGN_FLAG_$$foo.G, _WRITE_HAS_OCCURRED_$$foo.H, _WRITE_READ_BENIGN_FLAG_$$foo.H, _WRITE_READ_BENIGN_FLAG_$$foo.H, _WRITE_HAS_OCCURRED_$$foo.I, _WRITE_READ_BENIGN_FLAG_$$foo.I, _WRITE_READ_BENIGN_FLAG_$$foo.I, _WRITE_HAS_OCCURRED_$$foo.J, _WRITE_READ_BENIGN_FLAG_$$foo.J, _WRITE_READ_BENIGN_FLAG_$$foo.J, _NOT_ACCESSED_$$foo.G, _NOT_ACCESSED_$$foo.H, _NOT_ACCESSED_$$foo.I, _NOT_ACCESSED_$$foo.J, _TRACKING, _READ_HAS_OCCURRED_$$foo.G, _READ_HAS_OCCURRED_$$foo.H, _READ_HAS_OCCURRED_$$foo.I, _READ_HAS_OCCURRED_$$foo.J;

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

  __partitioned_block_$entry_0:
    call _LOG_WRITE_$$foo.G(true, local_id_x$1, local_id_x$1, $$foo.G[1bv1][local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.G(true, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 3} true;
    call _CHECK_WRITE_$$foo.G(true, local_id_x$2, local_id_x$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$foo.G"} true;
    $$foo.G[1bv1][local_id_x$1] := local_id_x$1;
    $$foo.G[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] := local_id_x$2;
    assume _NOT_ACCESSED_$$foo.G != local_id_x$1 && _NOT_ACCESSED_$$foo.G != local_id_x$2;
    call _LOG_WRITE_$$foo.H(true, local_id_x$1, local_id_x$1, $$foo.H[1bv1][local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.H(true, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 4} true;
    call _CHECK_WRITE_$$foo.H(true, local_id_x$2, local_id_x$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$foo.H"} true;
    $$foo.H[1bv1][local_id_x$1] := local_id_x$1;
    $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] := local_id_x$2;
    assume _NOT_ACCESSED_$$foo.H != local_id_x$1 && _NOT_ACCESSED_$$foo.H != local_id_x$2;
    call _LOG_WRITE_$$foo.I(true, local_id_x$1, local_id_x$1, $$foo.I[1bv1][local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.I(true, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 5} true;
    call _CHECK_WRITE_$$foo.I(true, local_id_x$2, local_id_x$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$foo.I"} true;
    $$foo.I[1bv1][local_id_x$1] := local_id_x$1;
    $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] := local_id_x$2;
    assume _NOT_ACCESSED_$$foo.I != local_id_x$1 && _NOT_ACCESSED_$$foo.I != local_id_x$2;
    call _LOG_WRITE_$$foo.J(true, local_id_x$1, local_id_x$1, $$foo.J[1bv1][local_id_x$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.J(true, local_id_x$2);
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 6} true;
    call _CHECK_WRITE_$$foo.J(true, local_id_x$2, local_id_x$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$foo.J"} true;
    $$foo.J[1bv1][local_id_x$1] := local_id_x$1;
    $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] := local_id_x$2;
    assume _NOT_ACCESSED_$$foo.J != local_id_x$1 && _NOT_ACCESSED_$$foo.J != local_id_x$2;
    assert {:barrier_invariant true} {:sourceloc_num 7} {:thread 1} true ==> (if $$foo.G[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assert {:barrier_invariant_access_check true} {:sourceloc_num 7} {:thread 1} true ==> true ==> _NOT_ACCESSED_$$foo.G != local_id_x$1;
    assert {:barrier_invariant true} {:sourceloc_num 8} {:thread 1} true ==> (if $$foo.H[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assert {:barrier_invariant_access_check true} {:sourceloc_num 8} {:thread 1} true ==> true ==> _NOT_ACCESSED_$$foo.H != local_id_x$1;
    assert {:barrier_invariant true} {:sourceloc_num 9} {:thread 1} true ==> (if $$foo.I[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assert {:barrier_invariant_access_check true} {:sourceloc_num 9} {:thread 1} true ==> true ==> _NOT_ACCESSED_$$foo.I != local_id_x$1;
    assert {:barrier_invariant true} {:sourceloc_num 10} {:thread 1} true ==> (if $$foo.J[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assert {:barrier_invariant_access_check true} {:sourceloc_num 10} {:thread 1} true ==> true ==> _NOT_ACCESSED_$$foo.J != local_id_x$1;
    goto __partitioned_block_$entry_1;

  __partitioned_block_$entry_1:
    call $bugle_barrier_duplicated_0(1bv1, 0bv1);
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.G[1bv1][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.G[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.G[1bv1][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.G[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(2bv32, 0bv32) && BV32_SLT(2bv32, group_size_x) ==> (if $$foo.G[1bv1][2bv32] == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(2bv32, 0bv32) && BV32_SLT(2bv32, group_size_x) ==> (if $$foo.G[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][2bv32] == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(3bv32, 0bv32) && BV32_SLT(3bv32, group_size_x) ==> (if $$foo.G[1bv1][3bv32] == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(3bv32, 0bv32) && BV32_SLT(3bv32, group_size_x) ==> (if $$foo.G[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][3bv32] == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(4bv32, 0bv32) && BV32_SLT(4bv32, group_size_x) ==> (if $$foo.G[1bv1][4bv32] == 4bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(4bv32, 0bv32) && BV32_SLT(4bv32, group_size_x) ==> (if $$foo.G[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][4bv32] == 4bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(5bv32, 0bv32) && BV32_SLT(5bv32, group_size_x) ==> (if $$foo.G[1bv1][5bv32] == 5bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(5bv32, 0bv32) && BV32_SLT(5bv32, group_size_x) ==> (if $$foo.G[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][5bv32] == 5bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(6bv32, 0bv32) && BV32_SLT(6bv32, group_size_x) ==> (if $$foo.G[1bv1][6bv32] == 6bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(6bv32, 0bv32) && BV32_SLT(6bv32, group_size_x) ==> (if $$foo.G[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][6bv32] == 6bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(7bv32, 0bv32) && BV32_SLT(7bv32, group_size_x) ==> (if $$foo.G[1bv1][7bv32] == 7bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(7bv32, 0bv32) && BV32_SLT(7bv32, group_size_x) ==> (if $$foo.G[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][7bv32] == 7bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(8bv32, 0bv32) && BV32_SLT(8bv32, group_size_x) ==> (if $$foo.G[1bv1][8bv32] == 8bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(8bv32, 0bv32) && BV32_SLT(8bv32, group_size_x) ==> (if $$foo.G[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][8bv32] == 8bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(9bv32, 0bv32) && BV32_SLT(9bv32, group_size_x) ==> (if $$foo.G[1bv1][9bv32] == 9bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(9bv32, 0bv32) && BV32_SLT(9bv32, group_size_x) ==> (if $$foo.G[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][9bv32] == 9bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(10bv32, 0bv32) && BV32_SLT(10bv32, group_size_x) ==> (if $$foo.G[1bv1][10bv32] == 10bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(10bv32, 0bv32) && BV32_SLT(10bv32, group_size_x) ==> (if $$foo.G[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][10bv32] == 10bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(11bv32, 0bv32) && BV32_SLT(11bv32, group_size_x) ==> (if $$foo.G[1bv1][11bv32] == 11bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(11bv32, 0bv32) && BV32_SLT(11bv32, group_size_x) ==> (if $$foo.G[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][11bv32] == 11bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$1, 0bv32) && BV32_SLT(local_id_x$1, group_size_x) ==> (if $$foo.G[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$2, 0bv32) && BV32_SLT(local_id_x$2, group_size_x) ==> (if $$foo.G[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] == local_id_x$2 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.H[1bv1][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.H[1bv1][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(2bv32, 0bv32) && BV32_SLT(2bv32, group_size_x) ==> (if $$foo.H[1bv1][2bv32] == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(2bv32, 0bv32) && BV32_SLT(2bv32, group_size_x) ==> (if $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][2bv32] == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(3bv32, 0bv32) && BV32_SLT(3bv32, group_size_x) ==> (if $$foo.H[1bv1][3bv32] == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(3bv32, 0bv32) && BV32_SLT(3bv32, group_size_x) ==> (if $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][3bv32] == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(4bv32, 0bv32) && BV32_SLT(4bv32, group_size_x) ==> (if $$foo.H[1bv1][4bv32] == 4bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(4bv32, 0bv32) && BV32_SLT(4bv32, group_size_x) ==> (if $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][4bv32] == 4bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(5bv32, 0bv32) && BV32_SLT(5bv32, group_size_x) ==> (if $$foo.H[1bv1][5bv32] == 5bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(5bv32, 0bv32) && BV32_SLT(5bv32, group_size_x) ==> (if $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][5bv32] == 5bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(6bv32, 0bv32) && BV32_SLT(6bv32, group_size_x) ==> (if $$foo.H[1bv1][6bv32] == 6bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(6bv32, 0bv32) && BV32_SLT(6bv32, group_size_x) ==> (if $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][6bv32] == 6bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(7bv32, 0bv32) && BV32_SLT(7bv32, group_size_x) ==> (if $$foo.H[1bv1][7bv32] == 7bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(7bv32, 0bv32) && BV32_SLT(7bv32, group_size_x) ==> (if $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][7bv32] == 7bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(8bv32, 0bv32) && BV32_SLT(8bv32, group_size_x) ==> (if $$foo.H[1bv1][8bv32] == 8bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(8bv32, 0bv32) && BV32_SLT(8bv32, group_size_x) ==> (if $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][8bv32] == 8bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(9bv32, 0bv32) && BV32_SLT(9bv32, group_size_x) ==> (if $$foo.H[1bv1][9bv32] == 9bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(9bv32, 0bv32) && BV32_SLT(9bv32, group_size_x) ==> (if $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][9bv32] == 9bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(10bv32, 0bv32) && BV32_SLT(10bv32, group_size_x) ==> (if $$foo.H[1bv1][10bv32] == 10bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(10bv32, 0bv32) && BV32_SLT(10bv32, group_size_x) ==> (if $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][10bv32] == 10bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(11bv32, 0bv32) && BV32_SLT(11bv32, group_size_x) ==> (if $$foo.H[1bv1][11bv32] == 11bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(11bv32, 0bv32) && BV32_SLT(11bv32, group_size_x) ==> (if $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][11bv32] == 11bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(12bv32, 0bv32) && BV32_SLT(12bv32, group_size_x) ==> (if $$foo.H[1bv1][12bv32] == 12bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(12bv32, 0bv32) && BV32_SLT(12bv32, group_size_x) ==> (if $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][12bv32] == 12bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(13bv32, 0bv32) && BV32_SLT(13bv32, group_size_x) ==> (if $$foo.H[1bv1][13bv32] == 13bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(13bv32, 0bv32) && BV32_SLT(13bv32, group_size_x) ==> (if $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][13bv32] == 13bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$1, 0bv32) && BV32_SLT(local_id_x$1, group_size_x) ==> (if $$foo.H[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$2, 0bv32) && BV32_SLT(local_id_x$2, group_size_x) ==> (if $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] == local_id_x$2 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.I[1bv1][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.I[1bv1][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(2bv32, 0bv32) && BV32_SLT(2bv32, group_size_x) ==> (if $$foo.I[1bv1][2bv32] == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(2bv32, 0bv32) && BV32_SLT(2bv32, group_size_x) ==> (if $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][2bv32] == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(3bv32, 0bv32) && BV32_SLT(3bv32, group_size_x) ==> (if $$foo.I[1bv1][3bv32] == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(3bv32, 0bv32) && BV32_SLT(3bv32, group_size_x) ==> (if $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][3bv32] == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(4bv32, 0bv32) && BV32_SLT(4bv32, group_size_x) ==> (if $$foo.I[1bv1][4bv32] == 4bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(4bv32, 0bv32) && BV32_SLT(4bv32, group_size_x) ==> (if $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][4bv32] == 4bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(5bv32, 0bv32) && BV32_SLT(5bv32, group_size_x) ==> (if $$foo.I[1bv1][5bv32] == 5bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(5bv32, 0bv32) && BV32_SLT(5bv32, group_size_x) ==> (if $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][5bv32] == 5bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(6bv32, 0bv32) && BV32_SLT(6bv32, group_size_x) ==> (if $$foo.I[1bv1][6bv32] == 6bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(6bv32, 0bv32) && BV32_SLT(6bv32, group_size_x) ==> (if $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][6bv32] == 6bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(7bv32, 0bv32) && BV32_SLT(7bv32, group_size_x) ==> (if $$foo.I[1bv1][7bv32] == 7bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(7bv32, 0bv32) && BV32_SLT(7bv32, group_size_x) ==> (if $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][7bv32] == 7bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(8bv32, 0bv32) && BV32_SLT(8bv32, group_size_x) ==> (if $$foo.I[1bv1][8bv32] == 8bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(8bv32, 0bv32) && BV32_SLT(8bv32, group_size_x) ==> (if $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][8bv32] == 8bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(9bv32, 0bv32) && BV32_SLT(9bv32, group_size_x) ==> (if $$foo.I[1bv1][9bv32] == 9bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(9bv32, 0bv32) && BV32_SLT(9bv32, group_size_x) ==> (if $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][9bv32] == 9bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(10bv32, 0bv32) && BV32_SLT(10bv32, group_size_x) ==> (if $$foo.I[1bv1][10bv32] == 10bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(10bv32, 0bv32) && BV32_SLT(10bv32, group_size_x) ==> (if $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][10bv32] == 10bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(11bv32, 0bv32) && BV32_SLT(11bv32, group_size_x) ==> (if $$foo.I[1bv1][11bv32] == 11bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(11bv32, 0bv32) && BV32_SLT(11bv32, group_size_x) ==> (if $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][11bv32] == 11bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(12bv32, 0bv32) && BV32_SLT(12bv32, group_size_x) ==> (if $$foo.I[1bv1][12bv32] == 12bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(12bv32, 0bv32) && BV32_SLT(12bv32, group_size_x) ==> (if $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][12bv32] == 12bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(13bv32, 0bv32) && BV32_SLT(13bv32, group_size_x) ==> (if $$foo.I[1bv1][13bv32] == 13bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(13bv32, 0bv32) && BV32_SLT(13bv32, group_size_x) ==> (if $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][13bv32] == 13bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(14bv32, 0bv32) && BV32_SLT(14bv32, group_size_x) ==> (if $$foo.I[1bv1][14bv32] == 14bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(14bv32, 0bv32) && BV32_SLT(14bv32, group_size_x) ==> (if $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][14bv32] == 14bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(15bv32, 0bv32) && BV32_SLT(15bv32, group_size_x) ==> (if $$foo.I[1bv1][15bv32] == 15bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(15bv32, 0bv32) && BV32_SLT(15bv32, group_size_x) ==> (if $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][15bv32] == 15bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$1, 0bv32) && BV32_SLT(local_id_x$1, group_size_x) ==> (if $$foo.I[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$2, 0bv32) && BV32_SLT(local_id_x$2, group_size_x) ==> (if $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] == local_id_x$2 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.J[1bv1][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(0bv32, 0bv32) && BV32_SLT(0bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][0bv32] == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.J[1bv1][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(1bv32, 0bv32) && BV32_SLT(1bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][1bv32] == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(2bv32, 0bv32) && BV32_SLT(2bv32, group_size_x) ==> (if $$foo.J[1bv1][2bv32] == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(2bv32, 0bv32) && BV32_SLT(2bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][2bv32] == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(3bv32, 0bv32) && BV32_SLT(3bv32, group_size_x) ==> (if $$foo.J[1bv1][3bv32] == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(3bv32, 0bv32) && BV32_SLT(3bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][3bv32] == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(4bv32, 0bv32) && BV32_SLT(4bv32, group_size_x) ==> (if $$foo.J[1bv1][4bv32] == 4bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(4bv32, 0bv32) && BV32_SLT(4bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][4bv32] == 4bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(5bv32, 0bv32) && BV32_SLT(5bv32, group_size_x) ==> (if $$foo.J[1bv1][5bv32] == 5bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(5bv32, 0bv32) && BV32_SLT(5bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][5bv32] == 5bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(6bv32, 0bv32) && BV32_SLT(6bv32, group_size_x) ==> (if $$foo.J[1bv1][6bv32] == 6bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(6bv32, 0bv32) && BV32_SLT(6bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][6bv32] == 6bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(7bv32, 0bv32) && BV32_SLT(7bv32, group_size_x) ==> (if $$foo.J[1bv1][7bv32] == 7bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(7bv32, 0bv32) && BV32_SLT(7bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][7bv32] == 7bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(8bv32, 0bv32) && BV32_SLT(8bv32, group_size_x) ==> (if $$foo.J[1bv1][8bv32] == 8bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(8bv32, 0bv32) && BV32_SLT(8bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][8bv32] == 8bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(9bv32, 0bv32) && BV32_SLT(9bv32, group_size_x) ==> (if $$foo.J[1bv1][9bv32] == 9bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(9bv32, 0bv32) && BV32_SLT(9bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][9bv32] == 9bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(10bv32, 0bv32) && BV32_SLT(10bv32, group_size_x) ==> (if $$foo.J[1bv1][10bv32] == 10bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(10bv32, 0bv32) && BV32_SLT(10bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][10bv32] == 10bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(11bv32, 0bv32) && BV32_SLT(11bv32, group_size_x) ==> (if $$foo.J[1bv1][11bv32] == 11bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(11bv32, 0bv32) && BV32_SLT(11bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][11bv32] == 11bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(12bv32, 0bv32) && BV32_SLT(12bv32, group_size_x) ==> (if $$foo.J[1bv1][12bv32] == 12bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(12bv32, 0bv32) && BV32_SLT(12bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][12bv32] == 12bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(13bv32, 0bv32) && BV32_SLT(13bv32, group_size_x) ==> (if $$foo.J[1bv1][13bv32] == 13bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(13bv32, 0bv32) && BV32_SLT(13bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][13bv32] == 13bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(14bv32, 0bv32) && BV32_SLT(14bv32, group_size_x) ==> (if $$foo.J[1bv1][14bv32] == 14bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(14bv32, 0bv32) && BV32_SLT(14bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][14bv32] == 14bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(15bv32, 0bv32) && BV32_SLT(15bv32, group_size_x) ==> (if $$foo.J[1bv1][15bv32] == 15bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(15bv32, 0bv32) && BV32_SLT(15bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][15bv32] == 15bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(16bv32, 0bv32) && BV32_SLT(16bv32, group_size_x) ==> (if $$foo.J[1bv1][16bv32] == 16bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(16bv32, 0bv32) && BV32_SLT(16bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][16bv32] == 16bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(17bv32, 0bv32) && BV32_SLT(17bv32, group_size_x) ==> (if $$foo.J[1bv1][17bv32] == 17bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(17bv32, 0bv32) && BV32_SLT(17bv32, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][17bv32] == 17bv32 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$1, 0bv32) && BV32_SLT(local_id_x$1, group_size_x) ==> (if $$foo.J[1bv1][local_id_x$1] == local_id_x$1 then 1bv1 else 0bv1) != 0bv1;
    assume true ==> BV32_SGE(local_id_x$2, 0bv32) && BV32_SLT(local_id_x$2, group_size_x) ==> (if $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2] == local_id_x$2 then 1bv1 else 0bv1) != 0bv1;
    v0 := BV32_ULE($arbitrary, 11bv32);
    goto $truebb, $falsebb;

  $falsebb:
    assume {:partition} !v0;
    $0$1 := 0bv1;
    $0$2 := 0bv1;
    goto $land.end;

  $land.end:
    assume {:do_not_predicate} {:check_id "check_state_4"} {:captureState "check_state_4"} {:sourceloc} {:sourceloc_num 14} true;
    v1$1 := $$foo.G[1bv1][local_id_x$1];
    v1$2 := $$foo.G[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2];
    assume _NOT_ACCESSED_$$foo.G != local_id_x$1 && _NOT_ACCESSED_$$foo.G != local_id_x$2;
    assume {:do_not_predicate} {:check_id "check_state_5"} {:captureState "check_state_5"} {:sourceloc} {:sourceloc_num 15} true;
    v2$1 := $$foo.G[1bv1][$arbitrary];
    v2$2 := $$foo.G[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][$arbitrary];
    assume _NOT_ACCESSED_$$foo.G != $arbitrary && _NOT_ACCESSED_$$foo.G != $arbitrary;
    assert {:sourceloc_num 16} {:thread 1} (if $0$1 == 1bv1 ==> BV32_SGT(v1$1, v2$1) then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 16} {:thread 2} (if $0$2 == 1bv1 ==> BV32_SGT(v1$2, v2$2) then 1bv1 else 0bv1) != 0bv1;
    v3 := BV32_ULE($arbitrary, 13bv32);
    goto $truebb0, $falsebb0;

  $falsebb0:
    assume {:partition} !v3;
    $1$1 := 0bv1;
    $1$2 := 0bv1;
    goto $land.end44;

  $land.end44:
    assume {:do_not_predicate} {:check_id "check_state_6"} {:captureState "check_state_6"} {:sourceloc} {:sourceloc_num 19} true;
    v4$1 := $$foo.H[1bv1][local_id_x$1];
    v4$2 := $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2];
    assume _NOT_ACCESSED_$$foo.H != local_id_x$1 && _NOT_ACCESSED_$$foo.H != local_id_x$2;
    assume {:do_not_predicate} {:check_id "check_state_7"} {:captureState "check_state_7"} {:sourceloc} {:sourceloc_num 20} true;
    v5$1 := $$foo.H[1bv1][$arbitrary];
    v5$2 := $$foo.H[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][$arbitrary];
    assume _NOT_ACCESSED_$$foo.H != $arbitrary && _NOT_ACCESSED_$$foo.H != $arbitrary;
    assert {:sourceloc_num 21} {:thread 1} (if $1$1 == 1bv1 ==> BV32_SGT(v4$1, v5$1) then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 21} {:thread 2} (if $1$2 == 1bv1 ==> BV32_SGT(v4$2, v5$2) then 1bv1 else 0bv1) != 0bv1;
    v6 := BV32_ULE($arbitrary, 15bv32);
    goto $truebb1, $falsebb1;

  $falsebb1:
    assume {:partition} !v6;
    $2$1 := 0bv1;
    $2$2 := 0bv1;
    goto $land.end54;

  $land.end54:
    assume {:do_not_predicate} {:check_id "check_state_8"} {:captureState "check_state_8"} {:sourceloc} {:sourceloc_num 24} true;
    v7$1 := $$foo.I[1bv1][local_id_x$1];
    v7$2 := $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2];
    assume _NOT_ACCESSED_$$foo.I != local_id_x$1 && _NOT_ACCESSED_$$foo.I != local_id_x$2;
    assume {:do_not_predicate} {:check_id "check_state_9"} {:captureState "check_state_9"} {:sourceloc} {:sourceloc_num 25} true;
    v8$1 := $$foo.I[1bv1][$arbitrary];
    v8$2 := $$foo.I[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][$arbitrary];
    assume _NOT_ACCESSED_$$foo.I != $arbitrary && _NOT_ACCESSED_$$foo.I != $arbitrary;
    assert {:sourceloc_num 26} {:thread 1} (if $2$1 == 1bv1 ==> BV32_SGT(v7$1, v8$1) then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 26} {:thread 2} (if $2$2 == 1bv1 ==> BV32_SGT(v7$2, v8$2) then 1bv1 else 0bv1) != 0bv1;
    v9 := BV32_ULE($arbitrary, 17bv32);
    goto $truebb2, $falsebb2;

  $falsebb2:
    assume {:partition} !v9;
    $3$1 := 0bv1;
    $3$2 := 0bv1;
    goto $land.end64;

  $land.end64:
    assume {:do_not_predicate} {:check_id "check_state_10"} {:captureState "check_state_10"} {:sourceloc} {:sourceloc_num 29} true;
    v10$1 := $$foo.J[1bv1][local_id_x$1];
    v10$2 := $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][local_id_x$2];
    assume _NOT_ACCESSED_$$foo.J != local_id_x$1 && _NOT_ACCESSED_$$foo.J != local_id_x$2;
    assume {:do_not_predicate} {:check_id "check_state_11"} {:captureState "check_state_11"} {:sourceloc} {:sourceloc_num 30} true;
    v11$1 := $$foo.J[1bv1][$arbitrary];
    v11$2 := $$foo.J[(if group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 then 1bv1 else 0bv1)][$arbitrary];
    assume _NOT_ACCESSED_$$foo.J != $arbitrary && _NOT_ACCESSED_$$foo.J != $arbitrary;
    assert {:sourceloc_num 31} {:thread 1} (if $3$1 == 1bv1 ==> BV32_SGT(v10$1, v11$1) then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 31} {:thread 2} (if $3$2 == 1bv1 ==> BV32_SGT(v10$2, v11$2) then 1bv1 else 0bv1) != 0bv1;
    return;

  $truebb2:
    assume {:partition} v9;
    $3$1 := (if BV32_UGT(local_id_x$1, $arbitrary) then 1bv1 else 0bv1);
    $3$2 := (if BV32_UGT(local_id_x$2, $arbitrary) then 1bv1 else 0bv1);
    goto $land.end64;

  $truebb1:
    assume {:partition} v6;
    $2$1 := (if BV32_UGT(local_id_x$1, $arbitrary) then 1bv1 else 0bv1);
    $2$2 := (if BV32_UGT(local_id_x$2, $arbitrary) then 1bv1 else 0bv1);
    goto $land.end54;

  $truebb0:
    assume {:partition} v3;
    $1$1 := (if BV32_UGT(local_id_x$1, $arbitrary) then 1bv1 else 0bv1);
    $1$2 := (if BV32_UGT(local_id_x$2, $arbitrary) then 1bv1 else 0bv1);
    goto $land.end44;

  $truebb:
    assume {:partition} v0;
    $0$1 := (if BV32_UGT(local_id_x$1, $arbitrary) then 1bv1 else 0bv1);
    $0$2 := (if BV32_UGT(local_id_x$2, $arbitrary) then 1bv1 else 0bv1);
    goto $land.end;
}

procedure {:source_name "__barrier_invariant_13"} {:barrier_invariant} $__barrier_invariant_1313($instantiation1: bv32, $instantiation2: bv32, $instantiation3: bv32, $instantiation4: bv32, $instantiation5: bv32, $instantiation6: bv32, $instantiation7: bv32, $instantiation8: bv32, $instantiation9: bv32, $instantiation10: bv32, $instantiation11: bv32, $instantiation12: bv32, $expr$1: bv1, $instantiation13$1: bv32, $expr$2: bv1, $instantiation13$2: bv32);
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
  requires $instantiation11 == 10bv32;
  requires $instantiation12 == 11bv32;

procedure {:source_name "__barrier_invariant_15"} {:barrier_invariant} $__barrier_invariant_1515($instantiation1: bv32, $instantiation2: bv32, $instantiation3: bv32, $instantiation4: bv32, $instantiation5: bv32, $instantiation6: bv32, $instantiation7: bv32, $instantiation8: bv32, $instantiation9: bv32, $instantiation10: bv32, $instantiation11: bv32, $instantiation12: bv32, $instantiation13: bv32, $instantiation14: bv32, $expr$1: bv1, $instantiation15$1: bv32, $expr$2: bv1, $instantiation15$2: bv32);
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
  requires $instantiation11 == 10bv32;
  requires $instantiation12 == 11bv32;
  requires $instantiation13 == 12bv32;
  requires $instantiation14 == 13bv32;

procedure {:source_name "__barrier_invariant_17"} {:barrier_invariant} $__barrier_invariant_1717($instantiation1: bv32, $instantiation2: bv32, $instantiation3: bv32, $instantiation4: bv32, $instantiation5: bv32, $instantiation6: bv32, $instantiation7: bv32, $instantiation8: bv32, $instantiation9: bv32, $instantiation10: bv32, $instantiation11: bv32, $instantiation12: bv32, $instantiation13: bv32, $instantiation14: bv32, $instantiation15: bv32, $instantiation16: bv32, $expr$1: bv1, $instantiation17$1: bv32, $expr$2: bv1, $instantiation17$2: bv32);
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
  requires $instantiation11 == 10bv32;
  requires $instantiation12 == 11bv32;
  requires $instantiation13 == 12bv32;
  requires $instantiation14 == 13bv32;
  requires $instantiation15 == 14bv32;
  requires $instantiation16 == 15bv32;

procedure {:source_name "__barrier_invariant_19"} {:barrier_invariant} $__barrier_invariant_1919($instantiation1: bv32, $instantiation2: bv32, $instantiation3: bv32, $instantiation4: bv32, $instantiation5: bv32, $instantiation6: bv32, $instantiation7: bv32, $instantiation8: bv32, $instantiation9: bv32, $instantiation10: bv32, $instantiation11: bv32, $instantiation12: bv32, $instantiation13: bv32, $instantiation14: bv32, $instantiation15: bv32, $instantiation16: bv32, $instantiation17: bv32, $instantiation18: bv32, $expr$1: bv1, $instantiation19$1: bv32, $expr$2: bv1, $instantiation19$2: bv32);
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
  requires $instantiation11 == 10bv32;
  requires $instantiation12 == 11bv32;
  requires $instantiation13 == 12bv32;
  requires $instantiation14 == 13bv32;
  requires $instantiation15 == 14bv32;
  requires $instantiation16 == 15bv32;
  requires $instantiation17 == 16bv32;
  requires $instantiation18 == 17bv32;

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
  modifies $$foo.G, $$foo.H, $$foo.I, $$foo.J, _NOT_ACCESSED_$$foo.G, _NOT_ACCESSED_$$foo.H, _NOT_ACCESSED_$$foo.I, _NOT_ACCESSED_$$foo.J, _TRACKING;

var {:check_access} _NOT_ACCESSED_$$foo.G: bv32;

var {:check_access} _NOT_ACCESSED_$$foo.H: bv32;

var {:check_access} _NOT_ACCESSED_$$foo.I: bv32;

var {:check_access} _NOT_ACCESSED_$$foo.J: bv32;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;

const _WATCHED_VALUE_$$foo.G: bv32;

procedure {:inline 1} _LOG_READ_$$foo.G(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$foo.G;

implementation {:inline 1} _LOG_READ_$$foo.G(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$foo.G := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.G == _value then true else _READ_HAS_OCCURRED_$$foo.G);
    return;
}

procedure _CHECK_READ_$$foo.G(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.G && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$foo.G && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.G && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$foo.G: bool;

procedure {:inline 1} _LOG_WRITE_$$foo.G(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$foo.G, _WRITE_READ_BENIGN_FLAG_$$foo.G;

implementation {:inline 1} _LOG_WRITE_$$foo.G(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$foo.G := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.G == _value then true else _WRITE_HAS_OCCURRED_$$foo.G);
    _WRITE_READ_BENIGN_FLAG_$$foo.G := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.G == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$foo.G);
    return;
}

procedure _CHECK_WRITE_$$foo.G(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.G && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.G != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.G && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.G != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.G && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$foo.G(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$foo.G;

implementation {:inline 1} _LOG_ATOMIC_$$foo.G(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$foo.G := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$foo.G);
    return;
}

procedure _CHECK_ATOMIC_$$foo.G(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.G && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.G && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.G(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$foo.G;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.G(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$foo.G := (if _P && _WRITE_HAS_OCCURRED_$$foo.G && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$foo.G);
    return;
}

const _WATCHED_VALUE_$$foo.H: bv32;

procedure {:inline 1} _LOG_READ_$$foo.H(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$foo.H;

implementation {:inline 1} _LOG_READ_$$foo.H(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$foo.H := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.H == _value then true else _READ_HAS_OCCURRED_$$foo.H);
    return;
}

procedure _CHECK_READ_$$foo.H(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.H && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$foo.H && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.H && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$foo.H: bool;

procedure {:inline 1} _LOG_WRITE_$$foo.H(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$foo.H, _WRITE_READ_BENIGN_FLAG_$$foo.H;

implementation {:inline 1} _LOG_WRITE_$$foo.H(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$foo.H := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.H == _value then true else _WRITE_HAS_OCCURRED_$$foo.H);
    _WRITE_READ_BENIGN_FLAG_$$foo.H := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.H == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$foo.H);
    return;
}

procedure _CHECK_WRITE_$$foo.H(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.H && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.H != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.H && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.H != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.H && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$foo.H(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$foo.H;

implementation {:inline 1} _LOG_ATOMIC_$$foo.H(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$foo.H := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$foo.H);
    return;
}

procedure _CHECK_ATOMIC_$$foo.H(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.H && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.H && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.H(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$foo.H;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.H(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$foo.H := (if _P && _WRITE_HAS_OCCURRED_$$foo.H && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$foo.H);
    return;
}

const _WATCHED_VALUE_$$foo.I: bv32;

procedure {:inline 1} _LOG_READ_$$foo.I(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$foo.I;

implementation {:inline 1} _LOG_READ_$$foo.I(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$foo.I := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.I == _value then true else _READ_HAS_OCCURRED_$$foo.I);
    return;
}

procedure _CHECK_READ_$$foo.I(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.I && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$foo.I && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.I && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$foo.I: bool;

procedure {:inline 1} _LOG_WRITE_$$foo.I(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$foo.I, _WRITE_READ_BENIGN_FLAG_$$foo.I;

implementation {:inline 1} _LOG_WRITE_$$foo.I(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$foo.I := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.I == _value then true else _WRITE_HAS_OCCURRED_$$foo.I);
    _WRITE_READ_BENIGN_FLAG_$$foo.I := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.I == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$foo.I);
    return;
}

procedure _CHECK_WRITE_$$foo.I(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.I && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.I != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.I && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.I != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.I && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$foo.I(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$foo.I;

implementation {:inline 1} _LOG_ATOMIC_$$foo.I(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$foo.I := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$foo.I);
    return;
}

procedure _CHECK_ATOMIC_$$foo.I(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.I && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.I && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.I(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$foo.I;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.I(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$foo.I := (if _P && _WRITE_HAS_OCCURRED_$$foo.I && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$foo.I);
    return;
}

const _WATCHED_VALUE_$$foo.J: bv32;

procedure {:inline 1} _LOG_READ_$$foo.J(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$foo.J;

implementation {:inline 1} _LOG_READ_$$foo.J(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$foo.J := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.J == _value then true else _READ_HAS_OCCURRED_$$foo.J);
    return;
}

procedure _CHECK_READ_$$foo.J(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.J && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$foo.J && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.J && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$foo.J: bool;

procedure {:inline 1} _LOG_WRITE_$$foo.J(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$foo.J, _WRITE_READ_BENIGN_FLAG_$$foo.J;

implementation {:inline 1} _LOG_WRITE_$$foo.J(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$foo.J := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.J == _value then true else _WRITE_HAS_OCCURRED_$$foo.J);
    _WRITE_READ_BENIGN_FLAG_$$foo.J := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.J == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$foo.J);
    return;
}

procedure _CHECK_WRITE_$$foo.J(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.J && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.J != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.J && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.J != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.J && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$foo.J(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$foo.J;

implementation {:inline 1} _LOG_ATOMIC_$$foo.J(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$foo.J := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$foo.J);
    return;
}

procedure _CHECK_ATOMIC_$$foo.J(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.J && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.J && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.J(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$foo.J;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.J(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$foo.J := (if _P && _WRITE_HAS_OCCURRED_$$foo.J && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$foo.J);
    return;
}

var _TRACKING: bool;

implementation {:inline 1} $bugle_barrier_duplicated_0($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon14_Then, anon14_Else;

  anon14_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$foo.G;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$foo.G;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$foo.G;
    goto anon1;

  anon1:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$foo.H;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$foo.H;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$foo.H;
    goto anon2;

  anon2:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$foo.I;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$foo.I;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$foo.I;
    goto anon3;

  anon3:
    assume $0 != 0bv1 ==> !_READ_HAS_OCCURRED_$$foo.J;
    assume $0 != 0bv1 ==> !_WRITE_HAS_OCCURRED_$$foo.J;
    assume $0 != 0bv1 ==> !_ATOMIC_HAS_OCCURRED_$$foo.J;
    goto anon4;

  anon4:
    goto anon15_Then, anon15_Else;

  anon15_Else:
    assume {:partition} !($0 != 0bv1 || $0 != 0bv1);
    goto anon13;

  anon13:
    havoc _TRACKING;
    return;

  anon15_Then:
    assume {:partition} $0 != 0bv1 || $0 != 0bv1;
    havoc $$foo.G;
    goto anon6;

  anon6:
    havoc $$foo.H;
    goto anon7;

  anon7:
    havoc $$foo.I;
    goto anon8;

  anon8:
    havoc $$foo.J;
    goto anon9;

  anon9:
    havoc _NOT_ACCESSED_$$foo.G;
    goto anon10;

  anon10:
    havoc _NOT_ACCESSED_$$foo.H;
    goto anon11;

  anon11:
    havoc _NOT_ACCESSED_$$foo.I;
    goto anon12;

  anon12:
    havoc _NOT_ACCESSED_$$foo.J;
    goto anon13;

  anon14_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

