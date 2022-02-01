//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

axiom {:array_info "$$.compoundliteral40"} {:elem_width 32} {:source_name ".compoundliteral40"} {:source_elem_width 128} {:source_dimensions "1"} true;

axiom {:array_info "$$.compoundliteral49"} {:elem_width 32} {:source_name ".compoundliteral49"} {:source_elem_width 128} {:source_dimensions "1"} true;

const _WATCHED_OFFSET: bv32;

const {:global_offset_x} global_offset_x: bv32;

const {:global_offset_y} global_offset_y: bv32;

const {:global_offset_z} global_offset_z: bv32;

const {:group_size_x} group_size_x: bv32;

const {:group_size_y} group_size_y: bv32;

const {:group_size_z} group_size_z: bv32;

const {:num_groups_x} num_groups_x: bv32;

const {:num_groups_y} num_groups_y: bv32;

const {:num_groups_z} num_groups_z: bv32;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

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
  var v6$1: bv32;
  var v6$2: bv32;
  var v7$1: bv32;
  var v7$2: bv32;

  $entry:
    assert {:sourceloc_num 1} {:thread 1} (if true then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 2} {:thread 1} (if true then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 3} {:thread 1} (if true then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 4} {:thread 1} (if true then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 5} {:thread 1} (if true then 1bv1 else 0bv1) != 0bv1;
    $$.compoundliteral40$0bv32$1 := 0bv32;
    $$.compoundliteral40$0bv32$2 := 0bv32;
    $$.compoundliteral40$1bv32$1 := 1bv32;
    $$.compoundliteral40$1bv32$2 := 1bv32;
    $$.compoundliteral40$2bv32$1 := 2bv32;
    $$.compoundliteral40$2bv32$2 := 2bv32;
    $$.compoundliteral40$3bv32$1 := 0bv32;
    $$.compoundliteral40$3bv32$2 := 0bv32;
    v0$1 := $$.compoundliteral40$0bv32$1;
    v0$2 := $$.compoundliteral40$0bv32$2;
    v1$1 := $$.compoundliteral40$1bv32$1;
    v1$2 := $$.compoundliteral40$1bv32$2;
    v2$1 := $$.compoundliteral40$2bv32$1;
    v2$2 := $$.compoundliteral40$2bv32$2;
    v3$1 := $$.compoundliteral40$3bv32$1;
    v3$2 := $$.compoundliteral40$3bv32$2;
    assert {:sourceloc_num 14} {:thread 1} (if BV32_ADD(BV32_ADD(BV32_ADD(v0$1, v1$1), v2$1), 3bv32) == 6bv32 then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 14} {:thread 2} (if BV32_ADD(BV32_ADD(BV32_ADD(v0$2, v1$2), v2$2), 3bv32) == 6bv32 then 1bv1 else 0bv1) != 0bv1;
    $$.compoundliteral49$0bv32$1 := 1bv32;
    $$.compoundliteral49$0bv32$2 := 1bv32;
    $$.compoundliteral49$1bv32$1 := 2bv32;
    $$.compoundliteral49$1bv32$2 := 2bv32;
    $$.compoundliteral49$2bv32$1 := 3bv32;
    $$.compoundliteral49$2bv32$2 := 3bv32;
    $$.compoundliteral49$3bv32$1 := 0bv32;
    $$.compoundliteral49$3bv32$2 := 0bv32;
    v4$1 := $$.compoundliteral49$0bv32$1;
    v4$2 := $$.compoundliteral49$0bv32$2;
    v5$1 := $$.compoundliteral49$1bv32$1;
    v5$2 := $$.compoundliteral49$1bv32$2;
    v6$1 := $$.compoundliteral49$2bv32$1;
    v6$2 := $$.compoundliteral49$2bv32$2;
    v7$1 := $$.compoundliteral49$3bv32$1;
    v7$2 := $$.compoundliteral49$3bv32$2;
    assert {:sourceloc_num 23} {:thread 1} (if BV32_ADD(BV32_ADD(v4$1, v5$1), v6$1) == 6bv32 then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 23} {:thread 2} (if BV32_ADD(BV32_ADD(v4$2, v5$2), v6$2) == 6bv32 then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 24} {:thread 1} (if BV32_ADD(BV32_ADD(6bv32, v1$1), v5$1) == 9bv32 then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 24} {:thread 2} (if BV32_ADD(BV32_ADD(6bv32, v1$2), v5$2) == 9bv32 then 1bv1 else 0bv1) != 0bv1;
    return;
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

var $$.compoundliteral40$0bv32$1: bv32;

var $$.compoundliteral40$0bv32$2: bv32;

var $$.compoundliteral40$1bv32$1: bv32;

var $$.compoundliteral40$1bv32$2: bv32;

var $$.compoundliteral40$2bv32$1: bv32;

var $$.compoundliteral40$2bv32$2: bv32;

var $$.compoundliteral40$3bv32$1: bv32;

var $$.compoundliteral40$3bv32$2: bv32;

var $$.compoundliteral49$0bv32$1: bv32;

var $$.compoundliteral49$0bv32$2: bv32;

var $$.compoundliteral49$1bv32$1: bv32;

var $$.compoundliteral49$1bv32$2: bv32;

var $$.compoundliteral49$2bv32$1: bv32;

var $$.compoundliteral49$2bv32$2: bv32;

var $$.compoundliteral49$3bv32$1: bv32;

var $$.compoundliteral49$3bv32$2: bv32;

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
