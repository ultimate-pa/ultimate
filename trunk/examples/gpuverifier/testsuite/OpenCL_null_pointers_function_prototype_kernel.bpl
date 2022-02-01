//#Unsafe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP8(x: [bv32]bv8, y: bv32) returns (z$1: bv8, A$1: [bv32]bv8, z$2: bv8, A$2: [bv32]bv8);

var {:source_name "x"} $$x$1: [bv32]bv8;

var {:source_name "x"} $$x$2: [bv32]bv8;

axiom {:array_info "$$x"} {:elem_width 8} {:source_name "x"} {:source_elem_width 32} {:source_dimensions "1"} true;

const $arrayId$$x: arrayId;

axiom $arrayId$$x == 1bv2;

type ptr = bv32;

type arrayId = bv2;

function {:inline true} MKPTR(base: arrayId, offset: bv32) : ptr
{
  base ++ offset[30:0]
}

function {:inline true} base#MKPTR(p: ptr) : arrayId
{
  p[32:30]
}

function {:inline true} offset#MKPTR(p: ptr) : bv32
{
  0bv2 ++ p[30:0]
}

const $arrayId$$null$: arrayId;

axiom $arrayId$$null$ == 0bv2;

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

function FADD32(bv32, bv32) : bv32;

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
  var v0$1: ptr;
  var v0$2: ptr;
  var v1$1: bv8;
  var v1$2: bv8;
  var v2$1: bv8;
  var v2$2: bv8;
  var v3$1: bv8;
  var v3$2: bv8;
  var v4$1: bv8;
  var v4$2: bv8;
  var v5$1: bv32;
  var v5$2: bv32;
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
  var p6$1: bool;
  var p6$2: bool;
  var p7$1: bool;
  var p7$2: bool;
  var p8$1: bool;
  var p8$2: bool;
  var p9$1: bool;
  var p9$2: bool;
  var p10$1: bool;
  var p10$2: bool;
  var p11$1: bool;
  var p11$2: bool;
  var p12$1: bool;
  var p12$2: bool;
  var p13$1: bool;
  var p13$2: bool;
  var p14$1: bool;
  var p14$2: bool;
  var p15$1: bool;
  var p15$2: bool;

  $entry:
    $$x$1[0bv32] := 0bv8;
    $$x$2[0bv32] := 0bv8;
    $$x$1[1bv32] := 0bv8;
    $$x$2[1bv32] := 0bv8;
    $$x$1[2bv32] := 0bv8;
    $$x$2[2bv32] := 0bv8;
    $$x$1[3bv32] := 0bv8;
    $$x$2[3bv32] := 0bv8;
    call v0$1, v0$2 := $bar(0bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "$bar"} true;
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
    p6$1 := false;
    p6$2 := false;
    p7$1 := false;
    p7$2 := false;
    p8$1 := false;
    p8$2 := false;
    p9$1 := false;
    p9$2 := false;
    p10$1 := false;
    p10$2 := false;
    p11$1 := false;
    p11$2 := false;
    p12$1 := false;
    p12$2 := false;
    p13$1 := false;
    p13$2 := false;
    p14$1 := false;
    p14$2 := false;
    p15$1 := false;
    p15$2 := false;
    p0$1 := (if base#MKPTR(v0$1) == $arrayId$$x then base#MKPTR(v0$1) == $arrayId$$x else p0$1);
    p0$2 := (if base#MKPTR(v0$2) == $arrayId$$x then base#MKPTR(v0$2) == $arrayId$$x else p0$2);
    p1$1 := (if base#MKPTR(v0$1) != $arrayId$$x then base#MKPTR(v0$1) != $arrayId$$x else p1$1);
    p1$2 := (if base#MKPTR(v0$2) != $arrayId$$x then base#MKPTR(v0$2) != $arrayId$$x else p1$2);
    v1$1 := (if p0$1 then $$x$1[offset#MKPTR(v0$1)] else v1$1);
    v1$2 := (if p0$2 then $$x$2[offset#MKPTR(v0$2)] else v1$2);
    assert {:bad_pointer_access} {:sourceloc_num 7} {:thread 1} p1$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 7} {:thread 2} p1$2 ==> false;
    p2$1 := (if base#MKPTR(v0$1) == $arrayId$$x then base#MKPTR(v0$1) == $arrayId$$x else p2$1);
    p2$2 := (if base#MKPTR(v0$2) == $arrayId$$x then base#MKPTR(v0$2) == $arrayId$$x else p2$2);
    p3$1 := (if base#MKPTR(v0$1) != $arrayId$$x then base#MKPTR(v0$1) != $arrayId$$x else p3$1);
    p3$2 := (if base#MKPTR(v0$2) != $arrayId$$x then base#MKPTR(v0$2) != $arrayId$$x else p3$2);
    v2$1 := (if p2$1 then $$x$1[BV32_ADD(offset#MKPTR(v0$1), 1bv32)] else v2$1);
    v2$2 := (if p2$2 then $$x$2[BV32_ADD(offset#MKPTR(v0$2), 1bv32)] else v2$2);
    assert {:bad_pointer_access} {:sourceloc_num 9} {:thread 1} p3$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 9} {:thread 2} p3$2 ==> false;
    p4$1 := (if base#MKPTR(v0$1) == $arrayId$$x then base#MKPTR(v0$1) == $arrayId$$x else p4$1);
    p4$2 := (if base#MKPTR(v0$2) == $arrayId$$x then base#MKPTR(v0$2) == $arrayId$$x else p4$2);
    p5$1 := (if base#MKPTR(v0$1) != $arrayId$$x then base#MKPTR(v0$1) != $arrayId$$x else p5$1);
    p5$2 := (if base#MKPTR(v0$2) != $arrayId$$x then base#MKPTR(v0$2) != $arrayId$$x else p5$2);
    v3$1 := (if p4$1 then $$x$1[BV32_ADD(offset#MKPTR(v0$1), 2bv32)] else v3$1);
    v3$2 := (if p4$2 then $$x$2[BV32_ADD(offset#MKPTR(v0$2), 2bv32)] else v3$2);
    assert {:bad_pointer_access} {:sourceloc_num 11} {:thread 1} p5$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 11} {:thread 2} p5$2 ==> false;
    p6$1 := (if base#MKPTR(v0$1) == $arrayId$$x then base#MKPTR(v0$1) == $arrayId$$x else p6$1);
    p6$2 := (if base#MKPTR(v0$2) == $arrayId$$x then base#MKPTR(v0$2) == $arrayId$$x else p6$2);
    p7$1 := (if base#MKPTR(v0$1) != $arrayId$$x then base#MKPTR(v0$1) != $arrayId$$x else p7$1);
    p7$2 := (if base#MKPTR(v0$2) != $arrayId$$x then base#MKPTR(v0$2) != $arrayId$$x else p7$2);
    v4$1 := (if p6$1 then $$x$1[BV32_ADD(offset#MKPTR(v0$1), 3bv32)] else v4$1);
    v4$2 := (if p6$2 then $$x$2[BV32_ADD(offset#MKPTR(v0$2), 3bv32)] else v4$2);
    assert {:bad_pointer_access} {:sourceloc_num 13} {:thread 1} p7$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 13} {:thread 2} p7$2 ==> false;
    v5$1 := FADD32(v4$1 ++ v3$1 ++ v2$1 ++ v1$1, 1065353216bv32);
    v5$2 := FADD32(v4$2 ++ v3$2 ++ v2$2 ++ v1$2, 1065353216bv32);
    p8$1 := (if base#MKPTR(v0$1) == $arrayId$$x then base#MKPTR(v0$1) == $arrayId$$x else p8$1);
    p8$2 := (if base#MKPTR(v0$2) == $arrayId$$x then base#MKPTR(v0$2) == $arrayId$$x else p8$2);
    p9$1 := (if base#MKPTR(v0$1) != $arrayId$$x then base#MKPTR(v0$1) != $arrayId$$x else p9$1);
    p9$2 := (if base#MKPTR(v0$2) != $arrayId$$x then base#MKPTR(v0$2) != $arrayId$$x else p9$2);
    $$x$1[offset#MKPTR(v0$1)] := (if p8$1 then v5$1[8:0] else $$x$1[offset#MKPTR(v0$1)]);
    $$x$2[offset#MKPTR(v0$2)] := (if p8$2 then v5$2[8:0] else $$x$2[offset#MKPTR(v0$2)]);
    assert {:bad_pointer_access} {:sourceloc_num 15} {:thread 1} p9$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 15} {:thread 2} p9$2 ==> false;
    p10$1 := (if base#MKPTR(v0$1) == $arrayId$$x then base#MKPTR(v0$1) == $arrayId$$x else p10$1);
    p10$2 := (if base#MKPTR(v0$2) == $arrayId$$x then base#MKPTR(v0$2) == $arrayId$$x else p10$2);
    p11$1 := (if base#MKPTR(v0$1) != $arrayId$$x then base#MKPTR(v0$1) != $arrayId$$x else p11$1);
    p11$2 := (if base#MKPTR(v0$2) != $arrayId$$x then base#MKPTR(v0$2) != $arrayId$$x else p11$2);
    $$x$1[BV32_ADD(offset#MKPTR(v0$1), 1bv32)] := (if p10$1 then v5$1[16:8] else $$x$1[BV32_ADD(offset#MKPTR(v0$1), 1bv32)]);
    $$x$2[BV32_ADD(offset#MKPTR(v0$2), 1bv32)] := (if p10$2 then v5$2[16:8] else $$x$2[BV32_ADD(offset#MKPTR(v0$2), 1bv32)]);
    assert {:bad_pointer_access} {:sourceloc_num 17} {:thread 1} p11$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 17} {:thread 2} p11$2 ==> false;
    p12$1 := (if base#MKPTR(v0$1) == $arrayId$$x then base#MKPTR(v0$1) == $arrayId$$x else p12$1);
    p12$2 := (if base#MKPTR(v0$2) == $arrayId$$x then base#MKPTR(v0$2) == $arrayId$$x else p12$2);
    p13$1 := (if base#MKPTR(v0$1) != $arrayId$$x then base#MKPTR(v0$1) != $arrayId$$x else p13$1);
    p13$2 := (if base#MKPTR(v0$2) != $arrayId$$x then base#MKPTR(v0$2) != $arrayId$$x else p13$2);
    $$x$1[BV32_ADD(offset#MKPTR(v0$1), 2bv32)] := (if p12$1 then v5$1[24:16] else $$x$1[BV32_ADD(offset#MKPTR(v0$1), 2bv32)]);
    $$x$2[BV32_ADD(offset#MKPTR(v0$2), 2bv32)] := (if p12$2 then v5$2[24:16] else $$x$2[BV32_ADD(offset#MKPTR(v0$2), 2bv32)]);
    assert {:bad_pointer_access} {:sourceloc_num 19} {:thread 1} p13$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 19} {:thread 2} p13$2 ==> false;
    p14$1 := (if base#MKPTR(v0$1) == $arrayId$$x then base#MKPTR(v0$1) == $arrayId$$x else p14$1);
    p14$2 := (if base#MKPTR(v0$2) == $arrayId$$x then base#MKPTR(v0$2) == $arrayId$$x else p14$2);
    p15$1 := (if base#MKPTR(v0$1) != $arrayId$$x then base#MKPTR(v0$1) != $arrayId$$x else p15$1);
    p15$2 := (if base#MKPTR(v0$2) != $arrayId$$x then base#MKPTR(v0$2) != $arrayId$$x else p15$2);
    $$x$1[BV32_ADD(offset#MKPTR(v0$1), 3bv32)] := (if p14$1 then v5$1[32:24] else $$x$1[BV32_ADD(offset#MKPTR(v0$1), 3bv32)]);
    $$x$2[BV32_ADD(offset#MKPTR(v0$2), 3bv32)] := (if p14$2 then v5$2[32:24] else $$x$2[BV32_ADD(offset#MKPTR(v0$2), 3bv32)]);
    assert {:bad_pointer_access} {:sourceloc_num 21} {:thread 1} p15$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 21} {:thread 2} p15$2 ==> false;
    return;
}

procedure {:source_name "bar"} $bar($0: bv32) returns ($ret$1: ptr, $ret$2: ptr);
  requires $0 == 0bv32;

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

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
