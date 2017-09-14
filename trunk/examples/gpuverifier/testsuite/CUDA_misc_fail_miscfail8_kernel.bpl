//#Unsafe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

axiom {:array_info "$$agg.tmp1"} {:elem_width 32} {:source_name "agg.tmp1"} {:source_elem_width 64} {:source_dimensions "1"} true;

axiom {:array_info "$$A.val"} {:elem_width 32} {:source_name "A.val"} {:source_elem_width 64} {:source_dimensions "1"} true;

axiom {:array_info "$$agg.tmp"} {:elem_width 32} {:source_name "agg.tmp"} {:source_elem_width 64} {:source_dimensions "1"} true;

const _WATCHED_OFFSET: bv32;

const {:group_size_x} group_size_x: bv32;

const {:group_size_y} group_size_y: bv32;

const {:group_size_z} group_size_z: bv32;

const {:num_groups_x} num_groups_x: bv32;

const {:num_groups_y} num_groups_y: bv32;

const {:num_groups_z} num_groups_z: bv32;

procedure {:source_name "test"} ULTIMATE.start($A: bv64);
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

implementation {:source_name "test"} ULTIMATE.start($A: bv64)
{
  var v0$1: bv32;
  var v0$2: bv32;
  var v1$1: bv32;
  var v1$2: bv32;
  var v2$1: bv32;
  var v2$2: bv32;
  var v3$1: bv32;
  var v3$2: bv32;

  $entry:
    $$A.val$0bv32$1 := $A[32:0];
    $$A.val$0bv32$2 := $A[32:0];
    $$A.val$1bv32$1 := $A[64:32];
    $$A.val$1bv32$2 := $A[64:32];
    v0$1 := $$A.val$0bv32$1;
    v0$2 := $$A.val$0bv32$2;
    $$agg.tmp$0bv32$1 := v0$1;
    $$agg.tmp$0bv32$2 := v0$2;
    v1$1 := $$A.val$1bv32$1;
    v1$2 := $$A.val$1bv32$2;
    $$agg.tmp$1bv32$1 := v1$1;
    $$agg.tmp$1bv32$2 := v1$2;
    v2$1 := $$agg.tmp$0bv32$1;
    v2$2 := $$agg.tmp$0bv32$2;
    $$agg.tmp1$0bv32$1 := v2$1;
    $$agg.tmp1$0bv32$2 := v2$2;
    v3$1 := $$agg.tmp$1bv32$1;
    v3$2 := $$agg.tmp$1bv32$2;
    $$agg.tmp1$1bv32$1 := v3$1;
    $$agg.tmp1$1bv32$2 := v3$2;
    assert {:sourceloc_num 11} {:thread 1} false;
    return;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 2bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 2bv32 then 1bv1 else 0bv1) != 0bv1;

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

var $$agg.tmp1$0bv32$1: bv32;

var $$agg.tmp1$0bv32$2: bv32;

var $$agg.tmp1$1bv32$1: bv32;

var $$agg.tmp1$1bv32$2: bv32;

var $$A.val$0bv32$1: bv32;

var $$A.val$0bv32$2: bv32;

var $$A.val$1bv32$1: bv32;

var $$A.val$1bv32$2: bv32;

var $$agg.tmp$0bv32$1: bv32;

var $$agg.tmp$0bv32$2: bv32;

var $$agg.tmp$1bv32$1: bv32;

var $$agg.tmp$1bv32$2: bv32;

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
