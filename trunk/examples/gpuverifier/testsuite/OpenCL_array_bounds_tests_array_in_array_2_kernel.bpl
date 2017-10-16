//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "L"} $$L$1: [bv32]bv32;

var {:source_name "L"} $$L$2: [bv32]bv32;

axiom {:array_info "$$L"} {:elem_width 32} {:source_name "L"} {:source_elem_width 32} {:source_dimensions "5"} true;

var {:source_name "K"} $$K$1: [bv32]bv32;

var {:source_name "K"} $$K$2: [bv32]bv32;

axiom {:array_info "$$K"} {:elem_width 32} {:source_name "K"} {:source_elem_width 32} {:source_dimensions "40"} true;

var {:source_name "foo.L"} {:constant} $$foo.L$1: [bv32]bv32;

var {:source_name "foo.L"} {:constant} $$foo.L$2: [bv32]bv32;

axiom {:array_info "$$foo.L"} {:constant} {:elem_width 32} {:source_name "foo.L"} {:source_elem_width 32} {:source_dimensions "5"} true;

const _WATCHED_OFFSET: bv32;

const {:global_offset_x} global_offset_x: bv32;

const {:global_offset_y} global_offset_y: bv32;

const {:global_offset_z} global_offset_z: bv32;

const {:group_id_x} group_id_x$1: bv32;

const {:group_id_x} group_id_x$2: bv32;

const {:group_id_y} group_id_y$1: bv32;

const {:group_id_y} group_id_y$2: bv32;

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

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

function {:builtin "bvurem"} BV32_UREM(bv32, bv32) : bv32;

procedure {:source_name "foo"} ULTIMATE.start();
  requires $$foo.L$1[0bv32] == 10bv32;
  requires $$foo.L$2[0bv32] == 10bv32;
  requires $$foo.L$1[1bv32] == 20bv32;
  requires $$foo.L$2[1bv32] == 20bv32;
  requires $$foo.L$1[2bv32] == 30bv32;
  requires $$foo.L$2[2bv32] == 30bv32;
  requires $$foo.L$1[3bv32] == 40bv32;
  requires $$foo.L$2[3bv32] == 40bv32;
  requires $$foo.L$1[4bv32] == 50bv32;
  requires $$foo.L$2[4bv32] == 50bv32;
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
  modifies _ARRAY_OFFSET_$$L, _ARRAY_OFFSET_$$K;

implementation {:source_name "foo"} ULTIMATE.start()
{
  var v0$1: bv32;
  var v0$2: bv32;
  var v1$1: bv32;
  var v1$2: bv32;
  var v2$1: bv32;
  var v2$2: bv32;
  var v3$1: bv32;
  var v3$2: bv32;
  var v4$1: bv32;
  var v4$2: bv32;
  var v5$1: bv32;
  var v5$2: bv32;

  $entry:
    v0$1 := $$foo.L$1[0bv32];
    v0$2 := $$foo.L$2[0bv32];
    _ARRAY_OFFSET_$$L := 0bv32;
    assume {:do_not_predicate} {:check_id "bounds_check_state_0"} {:captureState "bounds_check_state_0"} true;
    assert {:array_bounds} {:sourceloc_num 2} {:check_id "bounds_check_state_0"} {:array_name "$$L"} BV32_SGE(_ARRAY_OFFSET_$$L, 0bv32);
    assert {:array_bounds} {:sourceloc_num 2} {:check_id "bounds_check_state_0"} {:array_name "$$L"} BV32_SLT(_ARRAY_OFFSET_$$L, 5bv32);
    $$L$1[0bv32] := v0$1;
    $$L$2[0bv32] := v0$2;
    v1$1 := $$foo.L$1[1bv32];
    v1$2 := $$foo.L$2[1bv32];
    _ARRAY_OFFSET_$$L := 1bv32;
    assume {:do_not_predicate} {:check_id "bounds_check_state_1"} {:captureState "bounds_check_state_1"} true;
    assert {:array_bounds} {:sourceloc_num 4} {:check_id "bounds_check_state_1"} {:array_name "$$L"} BV32_SGE(_ARRAY_OFFSET_$$L, 0bv32);
    assert {:array_bounds} {:sourceloc_num 4} {:check_id "bounds_check_state_1"} {:array_name "$$L"} BV32_SLT(_ARRAY_OFFSET_$$L, 5bv32);
    $$L$1[1bv32] := v1$1;
    $$L$2[1bv32] := v1$2;
    v2$1 := $$foo.L$1[2bv32];
    v2$2 := $$foo.L$2[2bv32];
    _ARRAY_OFFSET_$$L := 2bv32;
    assume {:do_not_predicate} {:check_id "bounds_check_state_2"} {:captureState "bounds_check_state_2"} true;
    assert {:array_bounds} {:sourceloc_num 6} {:check_id "bounds_check_state_2"} {:array_name "$$L"} BV32_SGE(_ARRAY_OFFSET_$$L, 0bv32);
    assert {:array_bounds} {:sourceloc_num 6} {:check_id "bounds_check_state_2"} {:array_name "$$L"} BV32_SLT(_ARRAY_OFFSET_$$L, 5bv32);
    $$L$1[2bv32] := v2$1;
    $$L$2[2bv32] := v2$2;
    v3$1 := $$foo.L$1[3bv32];
    v3$2 := $$foo.L$2[3bv32];
    _ARRAY_OFFSET_$$L := 3bv32;
    assume {:do_not_predicate} {:check_id "bounds_check_state_3"} {:captureState "bounds_check_state_3"} true;
    assert {:array_bounds} {:sourceloc_num 8} {:check_id "bounds_check_state_3"} {:array_name "$$L"} BV32_SGE(_ARRAY_OFFSET_$$L, 0bv32);
    assert {:array_bounds} {:sourceloc_num 8} {:check_id "bounds_check_state_3"} {:array_name "$$L"} BV32_SLT(_ARRAY_OFFSET_$$L, 5bv32);
    $$L$1[3bv32] := v3$1;
    $$L$2[3bv32] := v3$2;
    v4$1 := $$foo.L$1[4bv32];
    v4$2 := $$foo.L$2[4bv32];
    _ARRAY_OFFSET_$$L := 4bv32;
    assume {:do_not_predicate} {:check_id "bounds_check_state_4"} {:captureState "bounds_check_state_4"} true;
    assert {:array_bounds} {:sourceloc_num 10} {:check_id "bounds_check_state_4"} {:array_name "$$L"} BV32_SGE(_ARRAY_OFFSET_$$L, 0bv32);
    assert {:array_bounds} {:sourceloc_num 10} {:check_id "bounds_check_state_4"} {:array_name "$$L"} BV32_SLT(_ARRAY_OFFSET_$$L, 5bv32);
    $$L$1[4bv32] := v4$1;
    $$L$2[4bv32] := v4$2;
    _ARRAY_OFFSET_$$L := BV32_UREM(BV32_ADD(BV32_MUL(group_id_y$1, group_size_y), local_id_y$1), 5bv32);
    _ARRAY_OFFSET_$$L := BV32_UREM(BV32_ADD(BV32_MUL(group_id_y$2, group_size_y), local_id_y$2), 5bv32);
    assume {:do_not_predicate} {:check_id "bounds_check_state_5"} {:captureState "bounds_check_state_5"} true;
    assert {:array_bounds} {:sourceloc_num 11} {:check_id "bounds_check_state_5"} {:array_name "$$L"} BV32_SGE(_ARRAY_OFFSET_$$L, 0bv32);
    assert {:array_bounds} {:sourceloc_num 11} {:check_id "bounds_check_state_5"} {:array_name "$$L"} BV32_SLT(_ARRAY_OFFSET_$$L, 5bv32);
    v5$1 := $$L$1[BV32_UREM(BV32_ADD(BV32_MUL(group_id_y$1, group_size_y), local_id_y$1), 5bv32)];
    v5$2 := $$L$2[BV32_UREM(BV32_ADD(BV32_MUL(group_id_y$2, group_size_y), local_id_y$2), 5bv32)];
    _ARRAY_OFFSET_$$K := BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$1, group_size_y), local_id_y$1), BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1));
    _ARRAY_OFFSET_$$K := BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$2, group_size_y), local_id_y$2), BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    assume {:do_not_predicate} {:check_id "bounds_check_state_6"} {:captureState "bounds_check_state_6"} true;
    assert {:array_bounds} {:sourceloc_num 12} {:check_id "bounds_check_state_6"} {:array_name "$$K"} BV32_SGE(_ARRAY_OFFSET_$$K, 0bv32);
    assert {:array_bounds} {:sourceloc_num 12} {:check_id "bounds_check_state_6"} {:array_name "$$K"} BV32_SLT(_ARRAY_OFFSET_$$K, 40bv32);
    $$K$1[BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$1, group_size_y), local_id_y$1), BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1))] := v5$1;
    $$K$2[BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$2, group_size_y), local_id_y$2), BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2))] := v5$2;
    return;
}

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 5bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_y == 8bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_x == 0bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_y == 0bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_z == 0bv32 then 1bv1 else 0bv1) != 0bv1;

const {:local_id_z} local_id_z$1: bv32;

const {:local_id_z} local_id_z$2: bv32;

const {:group_id_z} group_id_z$1: bv32;

const {:group_id_z} group_id_z$2: bv32;

var _ARRAY_OFFSET_$$L: bv32;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;

var _ARRAY_OFFSET_$$K: bv32;

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;
