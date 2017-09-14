//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

axiom {:array_info "$$a"} {:elem_width 32} {:source_name "a"} {:source_elem_width 128} {:source_dimensions "1"} true;

axiom {:array_info "$$b"} {:elem_width 32} {:source_name "b"} {:source_elem_width 128} {:source_dimensions "1"} true;

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

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;

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
  var v6$1: bv32;
  var v6$2: bv32;
  var v2$1: bv32;
  var v2$2: bv32;
  var v0$1: bv32;
  var v0$2: bv32;
  var v1$1: bv32;
  var v1$2: bv32;
  var v3$1: bv32;
  var v3$2: bv32;
  var v5$1: bv32;
  var v5$2: bv32;
  var v4$1: bv32;
  var v4$2: bv32;
  var v7$1: bv32;
  var v7$2: bv32;
  var v8$1: bv32;
  var v8$2: bv32;
  var v9$1: bv32;
  var v9$2: bv32;
  var v10$1: bv32;
  var v10$2: bv32;
  var v11$1: bv32;
  var v11$2: bv32;

  $entry:
    $$a$0bv32$1 := 1bv32;
    $$a$0bv32$2 := 1bv32;
    $$a$1bv32$1 := 2bv32;
    $$a$1bv32$2 := 2bv32;
    $$a$2bv32$1 := 3bv32;
    $$a$2bv32$2 := 3bv32;
    $$a$3bv32$1 := 0bv32;
    $$a$3bv32$2 := 0bv32;
    $$b$0bv32$1 := 2bv32;
    $$b$0bv32$2 := 2bv32;
    $$b$1bv32$1 := 3bv32;
    $$b$1bv32$2 := 3bv32;
    $$b$2bv32$1 := 4bv32;
    $$b$2bv32$2 := 4bv32;
    $$b$3bv32$1 := 1bv32;
    $$b$3bv32$2 := 1bv32;
    v0$1 := $$a$0bv32$1;
    v0$2 := $$a$0bv32$2;
    v1$1 := $$a$1bv32$1;
    v1$2 := $$a$1bv32$2;
    v2$1 := $$a$2bv32$1;
    v2$2 := $$a$2bv32$2;
    v3$1 := $$a$3bv32$1;
    v3$2 := $$a$3bv32$2;
    v4$1 := $$b$0bv32$1;
    v4$2 := $$b$0bv32$2;
    v5$1 := $$b$1bv32$1;
    v5$2 := $$b$1bv32$2;
    v6$1 := $$b$2bv32$1;
    v6$2 := $$b$2bv32$2;
    v7$1 := $$b$3bv32$1;
    v7$2 := $$b$3bv32$2;
    v8$1 := (if BV32_SLT(v4$1, v0$1) then v4$1 else v0$1);
    v8$2 := (if BV32_SLT(v4$2, v0$2) then v4$2 else v0$2);
    assert {:sourceloc_num 17} {:thread 1} (if v8$1 == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 17} {:thread 2} (if v8$2 == 1bv32 then 1bv1 else 0bv1) != 0bv1;
    v9$1 := (if BV32_SLT(v5$1, v1$1) then v5$1 else v1$1);
    v9$2 := (if BV32_SLT(v5$2, v1$2) then v5$2 else v1$2);
    assert {:sourceloc_num 18} {:thread 1} (if v9$1 == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 18} {:thread 2} (if v9$2 == 2bv32 then 1bv1 else 0bv1) != 0bv1;
    v10$1 := (if BV32_SLT(v6$1, v2$1) then v6$1 else v2$1);
    v10$2 := (if BV32_SLT(v6$2, v2$2) then v6$2 else v2$2);
    assert {:sourceloc_num 19} {:thread 1} (if v10$1 == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 19} {:thread 2} (if v10$2 == 3bv32 then 1bv1 else 0bv1) != 0bv1;
    v11$1 := (if BV32_SLT(v7$1, v3$1) then v7$1 else v3$1);
    v11$2 := (if BV32_SLT(v7$2, v3$2) then v7$2 else v3$2);
    assert {:sourceloc_num 20} {:thread 1} (if v11$1 == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    assert {:sourceloc_num 20} {:thread 2} (if v11$2 == 0bv32 then 1bv1 else 0bv1) != 0bv1;
    return;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 1024bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 1024bv32 then 1bv1 else 0bv1) != 0bv1;

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

var $$a$0bv32$1: bv32;

var $$a$0bv32$2: bv32;

var $$a$1bv32$1: bv32;

var $$a$1bv32$2: bv32;

var $$a$2bv32$1: bv32;

var $$a$2bv32$2: bv32;

var $$a$3bv32$1: bv32;

var $$a$3bv32$2: bv32;

var $$b$0bv32$1: bv32;

var $$b$0bv32$2: bv32;

var $$b$1bv32$1: bv32;

var $$b$1bv32$2: bv32;

var $$b$2bv32$1: bv32;

var $$b$2bv32$2: bv32;

var $$b$3bv32$1: bv32;

var $$b$3bv32$2: bv32;

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;
