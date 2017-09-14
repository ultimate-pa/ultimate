//#Unsafe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

axiom {:array_info "$$p"} {:global} {:elem_width 32} {:source_name "p"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$p: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$p: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$p: bool;

const $arrayId$$p: arrayId;

axiom $arrayId$$p == 1bv4;

axiom {:array_info "$$q"} {:global} {:elem_width 32} {:source_name "q"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$q: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$q: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$q: bool;

const $arrayId$$q: arrayId;

axiom $arrayId$$q == 2bv4;

axiom {:array_info "$$r"} {:global} {:elem_width 32} {:source_name "r"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$r: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$r: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$r: bool;

const $arrayId$$r: arrayId;

axiom $arrayId$$r == 3bv4;

var {:source_name "joint_handle_p"} $$joint_handle_p$1: [bv32]bv32;

var {:source_name "joint_handle_p"} $$joint_handle_p$2: [bv32]bv32;

axiom {:array_info "$$joint_handle_p"} {:elem_width 32} {:source_name "joint_handle_p"} {:source_elem_width 32} {:source_dimensions "1"} true;

const $arrayId$$joint_handle_p: arrayId;

axiom $arrayId$$joint_handle_p == 4bv4;

var {:source_name "joint_handle_q"} $$joint_handle_q$1: [bv32]bv32;

var {:source_name "joint_handle_q"} $$joint_handle_q$2: [bv32]bv32;

axiom {:array_info "$$joint_handle_q"} {:elem_width 32} {:source_name "joint_handle_q"} {:source_elem_width 32} {:source_dimensions "1"} true;

const $arrayId$$joint_handle_q: arrayId;

axiom $arrayId$$joint_handle_q == 5bv4;

var {:source_name "my_p"} {:group_shared} $$foo.my_p: [bv1][bv32]bv32;

axiom {:array_info "$$foo.my_p"} {:group_shared} {:elem_width 32} {:source_name "my_p"} {:source_elem_width 32} {:source_dimensions "64"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$foo.my_p: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$foo.my_p: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$foo.my_p: bool;

const $arrayId$$foo.my_p: arrayId;

axiom $arrayId$$foo.my_p == 6bv4;

var {:source_name "my_q"} {:group_shared} $$foo.my_q: [bv1][bv32]bv32;

axiom {:array_info "$$foo.my_q"} {:group_shared} {:elem_width 32} {:source_name "my_q"} {:source_elem_width 32} {:source_dimensions "64"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$foo.my_q: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$foo.my_q: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$foo.my_q: bool;

const $arrayId$$foo.my_q: arrayId;

axiom $arrayId$$foo.my_q == 7bv4;

var {:source_name "my_r"} {:group_shared} $$foo.my_r: [bv1][bv32]bv32;

axiom {:array_info "$$foo.my_r"} {:group_shared} {:elem_width 32} {:source_name "my_r"} {:source_elem_width 32} {:source_dimensions "64"} true;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$foo.my_r: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$foo.my_r: bool;

var {:race_checking} {:group_shared} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$foo.my_r: bool;

const $arrayId$$foo.my_r: arrayId;

axiom $arrayId$$foo.my_r == 8bv4;

type ptr = bv32;

type arrayId = bv4;

function {:inline true} MKPTR(base: arrayId, offset: bv32) : ptr
{
  base ++ offset[28:0]
}

function {:inline true} base#MKPTR(p: ptr) : arrayId
{
  p[32:28]
}

function {:inline true} offset#MKPTR(p: ptr) : bv32
{
  0bv4 ++ p[28:0]
}

const $arrayId$$null$: arrayId;

axiom $arrayId$$null$ == 0bv4;

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

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

function {:builtin "bvugt"} BV32_UGT(bv32, bv32) : bool;

procedure {:async_work_group_copy} _ASYNC_WORK_GROUP_COPY_32(dstOffset: bv32, size: bv32, src$1: [bv32]bv32, srcOffset$1: bv32, handle$1: bv32, src$2: [bv32]bv32, srcOffset$2: bv32, handle$2: bv32) returns (handle'$1: bv32, dst$1: [bv32]bv32, handle'$2: bv32, dst$2: [bv32]bv32);
  requires dstOffset == 0bv32;
  requires size == 64bv32;

procedure {:source_name "foo"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$p && !_WRITE_HAS_OCCURRED_$$p && !_ATOMIC_HAS_OCCURRED_$$p;
  requires !_READ_HAS_OCCURRED_$$q && !_WRITE_HAS_OCCURRED_$$q && !_ATOMIC_HAS_OCCURRED_$$q;
  requires !_READ_HAS_OCCURRED_$$r && !_WRITE_HAS_OCCURRED_$$r && !_ATOMIC_HAS_OCCURRED_$$r;
  requires !_READ_HAS_OCCURRED_$$foo.my_p && !_WRITE_HAS_OCCURRED_$$foo.my_p && !_ATOMIC_HAS_OCCURRED_$$foo.my_p;
  requires !_READ_HAS_OCCURRED_$$foo.my_q && !_WRITE_HAS_OCCURRED_$$foo.my_q && !_ATOMIC_HAS_OCCURRED_$$foo.my_q;
  requires !_READ_HAS_OCCURRED_$$foo.my_r && !_WRITE_HAS_OCCURRED_$$foo.my_r && !_ATOMIC_HAS_OCCURRED_$$foo.my_r;
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
  modifies _WRITE_HAS_OCCURRED_$$foo.my_p, _WRITE_READ_BENIGN_FLAG_$$foo.my_p, _WRITE_ASYNC_HANDLE_$$foo.my_p, _READ_HAS_OCCURRED_$$p, _READ_ASYNC_HANDLE_$$p, _WRITE_HAS_OCCURRED_$$foo.my_q, _WRITE_READ_BENIGN_FLAG_$$foo.my_q, _WRITE_ASYNC_HANDLE_$$foo.my_q, _READ_HAS_OCCURRED_$$q, _READ_ASYNC_HANDLE_$$q, _WRITE_HAS_OCCURRED_$$foo.my_r, _WRITE_READ_BENIGN_FLAG_$$foo.my_r, _WRITE_ASYNC_HANDLE_$$foo.my_r, _READ_HAS_OCCURRED_$$r, _READ_ASYNC_HANDLE_$$r;

implementation {:source_name "foo"} ULTIMATE.start()
{
  var $joint_handle_ptr.0$1: ptr;
  var $joint_handle_ptr.0$2: ptr;
  var v2$1: bool;
  var v2$2: bool;
  var v3$1: bv32;
  var v3$2: bv32;
  var v4$1: bv32;
  var v4$2: bv32;
  var v0$1: bv32;
  var v0$2: bv32;
  var v1$1: bv32;
  var v1$2: bv32;
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
    call v0$1, v0$2 := _ASYNC_WORK_GROUP_COPY_$$foo.my_p_$$p(true, 0bv32, BV32_MUL(64bv32, group_id_x$1), 64bv32, 0bv32, true, 0bv32, BV32_MUL(64bv32, group_id_x$2), 64bv32, 0bv32);
    $$joint_handle_p$1[0bv32] := v0$1;
    $$joint_handle_p$2[0bv32] := v0$2;
    call v1$1, v1$2 := _ASYNC_WORK_GROUP_COPY_$$foo.my_q_$$q(true, 0bv32, BV32_MUL(64bv32, group_id_x$1), 64bv32, 0bv32, true, 0bv32, BV32_MUL(64bv32, group_id_x$2), 64bv32, 0bv32);
    $$joint_handle_q$1[0bv32] := v1$1;
    $$joint_handle_q$2[0bv32] := v1$2;
    v2$1 := BV32_UGT(local_id_x$1, 13bv32);
    v2$2 := BV32_UGT(local_id_x$2, 13bv32);
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
    p0$1 := (if v2$1 then v2$1 else p0$1);
    p0$2 := (if v2$2 then v2$2 else p0$2);
    p1$1 := (if !v2$1 then !v2$1 else p1$1);
    p1$2 := (if !v2$2 then !v2$2 else p1$2);
    $joint_handle_ptr.0$1 := (if p0$1 then MKPTR($arrayId$$joint_handle_q, 0bv32) else $joint_handle_ptr.0$1);
    $joint_handle_ptr.0$2 := (if p0$2 then MKPTR($arrayId$$joint_handle_q, 0bv32) else $joint_handle_ptr.0$2);
    $joint_handle_ptr.0$1 := (if p1$1 then MKPTR($arrayId$$joint_handle_p, 0bv32) else $joint_handle_ptr.0$1);
    $joint_handle_ptr.0$2 := (if p1$2 then MKPTR($arrayId$$joint_handle_p, 0bv32) else $joint_handle_ptr.0$2);
    p2$1 := (if base#MKPTR($joint_handle_ptr.0$1) == $arrayId$$joint_handle_p then base#MKPTR($joint_handle_ptr.0$1) == $arrayId$$joint_handle_p else p2$1);
    p2$2 := (if base#MKPTR($joint_handle_ptr.0$2) == $arrayId$$joint_handle_p then base#MKPTR($joint_handle_ptr.0$2) == $arrayId$$joint_handle_p else p2$2);
    p3$1 := (if base#MKPTR($joint_handle_ptr.0$1) != $arrayId$$joint_handle_p then base#MKPTR($joint_handle_ptr.0$1) != $arrayId$$joint_handle_p else p3$1);
    p3$2 := (if base#MKPTR($joint_handle_ptr.0$2) != $arrayId$$joint_handle_p then base#MKPTR($joint_handle_ptr.0$2) != $arrayId$$joint_handle_p else p3$2);
    v3$1 := (if p2$1 then $$joint_handle_p$1[offset#MKPTR($joint_handle_ptr.0$1)] else v3$1);
    v3$2 := (if p2$2 then $$joint_handle_p$2[offset#MKPTR($joint_handle_ptr.0$2)] else v3$2);
    p4$1 := (if p3$1 && base#MKPTR($joint_handle_ptr.0$1) == $arrayId$$joint_handle_q then base#MKPTR($joint_handle_ptr.0$1) == $arrayId$$joint_handle_q else p4$1);
    p4$2 := (if p3$2 && base#MKPTR($joint_handle_ptr.0$2) == $arrayId$$joint_handle_q then base#MKPTR($joint_handle_ptr.0$2) == $arrayId$$joint_handle_q else p4$2);
    p5$1 := (if p3$1 && base#MKPTR($joint_handle_ptr.0$1) != $arrayId$$joint_handle_q then base#MKPTR($joint_handle_ptr.0$1) != $arrayId$$joint_handle_q else p5$1);
    p5$2 := (if p3$2 && base#MKPTR($joint_handle_ptr.0$2) != $arrayId$$joint_handle_q then base#MKPTR($joint_handle_ptr.0$2) != $arrayId$$joint_handle_q else p5$2);
    v3$1 := (if p4$1 then $$joint_handle_q$1[offset#MKPTR($joint_handle_ptr.0$1)] else v3$1);
    v3$2 := (if p4$2 then $$joint_handle_q$2[offset#MKPTR($joint_handle_ptr.0$2)] else v3$2);
    assert {:bad_pointer_access} {:sourceloc_num 9} {:thread 1} p5$1 ==> false;
    assert {:bad_pointer_access} {:sourceloc_num 9} {:thread 2} p5$2 ==> false;
    call v4$1, v4$2 := _ASYNC_WORK_GROUP_COPY_$$foo.my_r_$$r(true, 0bv32, BV32_MUL(64bv32, group_id_x$1), 64bv32, v3$1, true, 0bv32, BV32_MUL(64bv32, group_id_x$2), 64bv32, v3$2);
    return;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 64bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 128bv32 then 1bv1 else 0bv1) != 0bv1;

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

const _ASYNC_NO_HANDLE: bv32;

axiom _ASYNC_NO_HANDLE == 0bv32;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvuge"} BV32_UGE(bv32, bv32) : bool;

function {:builtin "bvult"} BV32_ULT(bv32, bv32) : bool;

procedure {:inline 1} _ASYNC_WORK_GROUP_COPY_$$foo.my_p_$$p(_P$1: bool, DstOffset$1: bv32, SrcOffset$1: bv32, Size$1: bv32, Handle$1: bv32, _P$2: bool, DstOffset$2: bv32, SrcOffset$2: bv32, Size$2: bv32, Handle$2: bv32) returns (ResultHandle$1: bv32, ResultHandle$2: bv32);
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> _P$1 == _P$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> _P$2 == _P$1;
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> DstOffset$1 == DstOffset$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> DstOffset$2 == DstOffset$1;
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> SrcOffset$1 == SrcOffset$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> SrcOffset$2 == SrcOffset$1;
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> Size$1 == Size$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> Size$2 == Size$1;
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> Handle$1 == Handle$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> Handle$2 == Handle$1;
  modifies _WRITE_HAS_OCCURRED_$$foo.my_p, _WRITE_READ_BENIGN_FLAG_$$foo.my_p, _WRITE_ASYNC_HANDLE_$$foo.my_p, _READ_HAS_OCCURRED_$$p, _READ_ASYNC_HANDLE_$$p;

implementation {:inline 1} _ASYNC_WORK_GROUP_COPY_$$foo.my_p_$$p(_P$1: bool, DstOffset$1: bv32, SrcOffset$1: bv32, Size$1: bv32, Handle$1: bv32, _P$2: bool, DstOffset$2: bv32, SrcOffset$2: bv32, Size$2: bv32, Handle$2: bv32) returns (ResultHandle$1: bv32, ResultHandle$2: bv32)
{
  var Index$1: bv32;
  var Index$2: bv32;
  var IdX$1: bv32;
  var IdX$2: bv32;
  var IdY$1: bv32;
  var IdY$2: bv32;
  var IdZ$1: bv32;
  var IdZ$2: bv32;
  var _abstracted_call_arg_0$1: bv32;
  var _abstracted_call_arg_0$2: bv32;
  var _abstracted_call_arg_1$1: bv32;
  var _abstracted_call_arg_1$2: bv32;
  var _abstracted_call_arg_2$1: bv32;
  var _abstracted_call_arg_2$2: bv32;
  var _abstracted_call_arg_3$1: bv32;
  var _abstracted_call_arg_3$2: bv32;
  var p0$1: bool;
  var p0$2: bool;
  var p1$1: bool;
  var p1$2: bool;
  var _HAVOC_bv32$1: bv32;
  var _HAVOC_bv32$2: bv32;

  entry:
    assume (_P$1 ==> ResultHandle$1 != _ASYNC_NO_HANDLE) && (_P$2 ==> ResultHandle$2 != _ASYNC_NO_HANDLE);
    ResultHandle$1 := (if _P$1 then (if Handle$1 == _ASYNC_NO_HANDLE then ResultHandle$1 else Handle$1) else ResultHandle$1);
    ResultHandle$2 := (if _P$2 then (if Handle$2 == _ASYNC_NO_HANDLE then ResultHandle$2 else Handle$2) else ResultHandle$2);
    assume (_P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> ResultHandle$1 == ResultHandle$2) && (_P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> ResultHandle$2 == ResultHandle$1);
    assume (_P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdX$1 == IdX$2) && (_P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdX$2 == IdX$1);
    assume (_P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdY$1 == IdY$2) && (_P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdY$2 == IdY$1);
    assume (_P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdZ$1 == IdZ$2) && (_P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdZ$2 == IdZ$1);
    p0$1 := false;
    p0$2 := false;
    p1$1 := false;
    p1$2 := false;
    p0$1 := (if _P$1 && IdX$1 == local_id_x$1 && IdY$1 == local_id_y$1 && IdZ$1 == local_id_z$1 then IdX$1 == local_id_x$1 && IdY$1 == local_id_y$1 && IdZ$1 == local_id_z$1 else p0$1);
    p0$2 := (if _P$2 && IdX$2 == local_id_x$2 && IdY$2 == local_id_y$2 && IdZ$2 == local_id_z$2 then IdX$2 == local_id_x$2 && IdY$2 == local_id_y$2 && IdZ$2 == local_id_z$2 else p0$2);
    assume (p0$1 ==> BV32_UGE(Index$1, 0bv32)) && (p0$2 ==> BV32_UGE(Index$2, 0bv32));
    assume (p0$1 ==> BV32_ULT(Index$1, Size$1)) && (p0$2 ==> BV32_ULT(Index$2, Size$2));
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    _abstracted_call_arg_0$1 := (if p0$1 then _HAVOC_bv32$1 else _abstracted_call_arg_0$1);
    _abstracted_call_arg_0$2 := (if p0$2 then _HAVOC_bv32$2 else _abstracted_call_arg_0$2);
    call _LOG_WRITE_$$foo.my_p(p0$1, BV32_ADD(DstOffset$1, Index$1), _abstracted_call_arg_0$1, $$foo.my_p[1bv1][BV32_ADD(DstOffset$1, Index$1)], ResultHandle$1);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 1} true;
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    _abstracted_call_arg_1$1 := (if p0$1 then _HAVOC_bv32$1 else _abstracted_call_arg_1$1);
    _abstracted_call_arg_1$2 := (if p0$2 then _HAVOC_bv32$2 else _abstracted_call_arg_1$2);
    call _CHECK_WRITE_$$foo.my_p(p0$2, BV32_ADD(DstOffset$2, Index$2), _abstracted_call_arg_1$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$foo.my_p"} true;
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    _abstracted_call_arg_2$1 := (if p0$1 then _HAVOC_bv32$1 else _abstracted_call_arg_2$1);
    _abstracted_call_arg_2$2 := (if p0$2 then _HAVOC_bv32$2 else _abstracted_call_arg_2$2);
    call _LOG_READ_$$p(p0$1, BV32_ADD(SrcOffset$1, Index$1), _abstracted_call_arg_2$1, ResultHandle$1);
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 1} true;
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    _abstracted_call_arg_3$1 := (if p0$1 then _HAVOC_bv32$1 else _abstracted_call_arg_3$1);
    _abstracted_call_arg_3$2 := (if p0$2 then _HAVOC_bv32$2 else _abstracted_call_arg_3$2);
    call _CHECK_READ_$$p(p0$2, BV32_ADD(SrcOffset$2, Index$2), _abstracted_call_arg_3$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$p"} true;
    return;
}

procedure {:inline 1} _ASYNC_WORK_GROUP_COPY_$$foo.my_q_$$q(_P$1: bool, DstOffset$1: bv32, SrcOffset$1: bv32, Size$1: bv32, Handle$1: bv32, _P$2: bool, DstOffset$2: bv32, SrcOffset$2: bv32, Size$2: bv32, Handle$2: bv32) returns (ResultHandle$1: bv32, ResultHandle$2: bv32);
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> _P$1 == _P$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> _P$2 == _P$1;
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> DstOffset$1 == DstOffset$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> DstOffset$2 == DstOffset$1;
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> SrcOffset$1 == SrcOffset$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> SrcOffset$2 == SrcOffset$1;
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> Size$1 == Size$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> Size$2 == Size$1;
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> Handle$1 == Handle$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> Handle$2 == Handle$1;
  modifies _WRITE_HAS_OCCURRED_$$foo.my_q, _WRITE_READ_BENIGN_FLAG_$$foo.my_q, _WRITE_ASYNC_HANDLE_$$foo.my_q, _READ_HAS_OCCURRED_$$q, _READ_ASYNC_HANDLE_$$q;

implementation {:inline 1} _ASYNC_WORK_GROUP_COPY_$$foo.my_q_$$q(_P$1: bool, DstOffset$1: bv32, SrcOffset$1: bv32, Size$1: bv32, Handle$1: bv32, _P$2: bool, DstOffset$2: bv32, SrcOffset$2: bv32, Size$2: bv32, Handle$2: bv32) returns (ResultHandle$1: bv32, ResultHandle$2: bv32)
{
  var Index$1: bv32;
  var Index$2: bv32;
  var IdX$1: bv32;
  var IdX$2: bv32;
  var IdY$1: bv32;
  var IdY$2: bv32;
  var IdZ$1: bv32;
  var IdZ$2: bv32;
  var _abstracted_call_arg_0$1: bv32;
  var _abstracted_call_arg_0$2: bv32;
  var _abstracted_call_arg_1$1: bv32;
  var _abstracted_call_arg_1$2: bv32;
  var _abstracted_call_arg_2$1: bv32;
  var _abstracted_call_arg_2$2: bv32;
  var _abstracted_call_arg_3$1: bv32;
  var _abstracted_call_arg_3$2: bv32;
  var p0$1: bool;
  var p0$2: bool;
  var p1$1: bool;
  var p1$2: bool;
  var _HAVOC_bv32$1: bv32;
  var _HAVOC_bv32$2: bv32;

  entry:
    assume (_P$1 ==> ResultHandle$1 != _ASYNC_NO_HANDLE) && (_P$2 ==> ResultHandle$2 != _ASYNC_NO_HANDLE);
    ResultHandle$1 := (if _P$1 then (if Handle$1 == _ASYNC_NO_HANDLE then ResultHandle$1 else Handle$1) else ResultHandle$1);
    ResultHandle$2 := (if _P$2 then (if Handle$2 == _ASYNC_NO_HANDLE then ResultHandle$2 else Handle$2) else ResultHandle$2);
    assume (_P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> ResultHandle$1 == ResultHandle$2) && (_P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> ResultHandle$2 == ResultHandle$1);
    assume (_P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdX$1 == IdX$2) && (_P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdX$2 == IdX$1);
    assume (_P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdY$1 == IdY$2) && (_P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdY$2 == IdY$1);
    assume (_P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdZ$1 == IdZ$2) && (_P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdZ$2 == IdZ$1);
    p0$1 := false;
    p0$2 := false;
    p1$1 := false;
    p1$2 := false;
    p0$1 := (if _P$1 && IdX$1 == local_id_x$1 && IdY$1 == local_id_y$1 && IdZ$1 == local_id_z$1 then IdX$1 == local_id_x$1 && IdY$1 == local_id_y$1 && IdZ$1 == local_id_z$1 else p0$1);
    p0$2 := (if _P$2 && IdX$2 == local_id_x$2 && IdY$2 == local_id_y$2 && IdZ$2 == local_id_z$2 then IdX$2 == local_id_x$2 && IdY$2 == local_id_y$2 && IdZ$2 == local_id_z$2 else p0$2);
    assume (p0$1 ==> BV32_UGE(Index$1, 0bv32)) && (p0$2 ==> BV32_UGE(Index$2, 0bv32));
    assume (p0$1 ==> BV32_ULT(Index$1, Size$1)) && (p0$2 ==> BV32_ULT(Index$2, Size$2));
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    _abstracted_call_arg_0$1 := (if p0$1 then _HAVOC_bv32$1 else _abstracted_call_arg_0$1);
    _abstracted_call_arg_0$2 := (if p0$2 then _HAVOC_bv32$2 else _abstracted_call_arg_0$2);
    call _LOG_WRITE_$$foo.my_q(p0$1, BV32_ADD(DstOffset$1, Index$1), _abstracted_call_arg_0$1, $$foo.my_q[1bv1][BV32_ADD(DstOffset$1, Index$1)], ResultHandle$1);
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 3} true;
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    _abstracted_call_arg_1$1 := (if p0$1 then _HAVOC_bv32$1 else _abstracted_call_arg_1$1);
    _abstracted_call_arg_1$2 := (if p0$2 then _HAVOC_bv32$2 else _abstracted_call_arg_1$2);
    call _CHECK_WRITE_$$foo.my_q(p0$2, BV32_ADD(DstOffset$2, Index$2), _abstracted_call_arg_1$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$foo.my_q"} true;
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    _abstracted_call_arg_2$1 := (if p0$1 then _HAVOC_bv32$1 else _abstracted_call_arg_2$1);
    _abstracted_call_arg_2$2 := (if p0$2 then _HAVOC_bv32$2 else _abstracted_call_arg_2$2);
    call _LOG_READ_$$q(p0$1, BV32_ADD(SrcOffset$1, Index$1), _abstracted_call_arg_2$1, ResultHandle$1);
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 3} true;
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    _abstracted_call_arg_3$1 := (if p0$1 then _HAVOC_bv32$1 else _abstracted_call_arg_3$1);
    _abstracted_call_arg_3$2 := (if p0$2 then _HAVOC_bv32$2 else _abstracted_call_arg_3$2);
    call _CHECK_READ_$$q(p0$2, BV32_ADD(SrcOffset$2, Index$2), _abstracted_call_arg_3$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$q"} true;
    return;
}

procedure {:inline 1} _ASYNC_WORK_GROUP_COPY_$$foo.my_r_$$r(_P$1: bool, DstOffset$1: bv32, SrcOffset$1: bv32, Size$1: bv32, Handle$1: bv32, _P$2: bool, DstOffset$2: bv32, SrcOffset$2: bv32, Size$2: bv32, Handle$2: bv32) returns (ResultHandle$1: bv32, ResultHandle$2: bv32);
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> _P$1 == _P$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> _P$2 == _P$1;
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> DstOffset$1 == DstOffset$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> DstOffset$2 == DstOffset$1;
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> SrcOffset$1 == SrcOffset$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> SrcOffset$2 == SrcOffset$1;
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> Size$1 == Size$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> Size$2 == Size$1;
  requires _P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> Handle$1 == Handle$2;
  requires _P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> Handle$2 == Handle$1;
  modifies _WRITE_HAS_OCCURRED_$$foo.my_r, _WRITE_READ_BENIGN_FLAG_$$foo.my_r, _WRITE_ASYNC_HANDLE_$$foo.my_r, _READ_HAS_OCCURRED_$$r, _READ_ASYNC_HANDLE_$$r;

implementation {:inline 1} _ASYNC_WORK_GROUP_COPY_$$foo.my_r_$$r(_P$1: bool, DstOffset$1: bv32, SrcOffset$1: bv32, Size$1: bv32, Handle$1: bv32, _P$2: bool, DstOffset$2: bv32, SrcOffset$2: bv32, Size$2: bv32, Handle$2: bv32) returns (ResultHandle$1: bv32, ResultHandle$2: bv32)
{
  var Index$1: bv32;
  var Index$2: bv32;
  var IdX$1: bv32;
  var IdX$2: bv32;
  var IdY$1: bv32;
  var IdY$2: bv32;
  var IdZ$1: bv32;
  var IdZ$2: bv32;
  var _abstracted_call_arg_0$1: bv32;
  var _abstracted_call_arg_0$2: bv32;
  var _abstracted_call_arg_1$1: bv32;
  var _abstracted_call_arg_1$2: bv32;
  var _abstracted_call_arg_2$1: bv32;
  var _abstracted_call_arg_2$2: bv32;
  var _abstracted_call_arg_3$1: bv32;
  var _abstracted_call_arg_3$2: bv32;
  var p0$1: bool;
  var p0$2: bool;
  var p1$1: bool;
  var p1$2: bool;
  var _HAVOC_bv32$1: bv32;
  var _HAVOC_bv32$2: bv32;

  entry:
    assume (_P$1 ==> ResultHandle$1 != _ASYNC_NO_HANDLE) && (_P$2 ==> ResultHandle$2 != _ASYNC_NO_HANDLE);
    ResultHandle$1 := (if _P$1 then (if Handle$1 == _ASYNC_NO_HANDLE then ResultHandle$1 else Handle$1) else ResultHandle$1);
    ResultHandle$2 := (if _P$2 then (if Handle$2 == _ASYNC_NO_HANDLE then ResultHandle$2 else Handle$2) else ResultHandle$2);
    assume (_P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> ResultHandle$1 == ResultHandle$2) && (_P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> ResultHandle$2 == ResultHandle$1);
    assume (_P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdX$1 == IdX$2) && (_P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdX$2 == IdX$1);
    assume (_P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdY$1 == IdY$2) && (_P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdY$2 == IdY$1);
    assume (_P$1 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdZ$1 == IdZ$2) && (_P$2 ==> group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 ==> IdZ$2 == IdZ$1);
    p0$1 := false;
    p0$2 := false;
    p1$1 := false;
    p1$2 := false;
    p0$1 := (if _P$1 && IdX$1 == local_id_x$1 && IdY$1 == local_id_y$1 && IdZ$1 == local_id_z$1 then IdX$1 == local_id_x$1 && IdY$1 == local_id_y$1 && IdZ$1 == local_id_z$1 else p0$1);
    p0$2 := (if _P$2 && IdX$2 == local_id_x$2 && IdY$2 == local_id_y$2 && IdZ$2 == local_id_z$2 then IdX$2 == local_id_x$2 && IdY$2 == local_id_y$2 && IdZ$2 == local_id_z$2 else p0$2);
    assume (p0$1 ==> BV32_UGE(Index$1, 0bv32)) && (p0$2 ==> BV32_UGE(Index$2, 0bv32));
    assume (p0$1 ==> BV32_ULT(Index$1, Size$1)) && (p0$2 ==> BV32_ULT(Index$2, Size$2));
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    _abstracted_call_arg_0$1 := (if p0$1 then _HAVOC_bv32$1 else _abstracted_call_arg_0$1);
    _abstracted_call_arg_0$2 := (if p0$2 then _HAVOC_bv32$2 else _abstracted_call_arg_0$2);
    call _LOG_WRITE_$$foo.my_r(p0$1, BV32_ADD(DstOffset$1, Index$1), _abstracted_call_arg_0$1, $$foo.my_r[1bv1][BV32_ADD(DstOffset$1, Index$1)], ResultHandle$1);
    assume {:do_not_predicate} {:check_id "check_state_4"} {:captureState "check_state_4"} {:sourceloc} {:sourceloc_num 10} true;
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    _abstracted_call_arg_1$1 := (if p0$1 then _HAVOC_bv32$1 else _abstracted_call_arg_1$1);
    _abstracted_call_arg_1$2 := (if p0$2 then _HAVOC_bv32$2 else _abstracted_call_arg_1$2);
    call _CHECK_WRITE_$$foo.my_r(p0$2, BV32_ADD(DstOffset$2, Index$2), _abstracted_call_arg_1$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$foo.my_r"} true;
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    _abstracted_call_arg_2$1 := (if p0$1 then _HAVOC_bv32$1 else _abstracted_call_arg_2$1);
    _abstracted_call_arg_2$2 := (if p0$2 then _HAVOC_bv32$2 else _abstracted_call_arg_2$2);
    call _LOG_READ_$$r(p0$1, BV32_ADD(SrcOffset$1, Index$1), _abstracted_call_arg_2$1, ResultHandle$1);
    assume {:do_not_predicate} {:check_id "check_state_5"} {:captureState "check_state_5"} {:sourceloc} {:sourceloc_num 10} true;
    havoc _HAVOC_bv32$1, _HAVOC_bv32$2;
    _abstracted_call_arg_3$1 := (if p0$1 then _HAVOC_bv32$1 else _abstracted_call_arg_3$1);
    _abstracted_call_arg_3$2 := (if p0$2 then _HAVOC_bv32$2 else _abstracted_call_arg_3$2);
    call _CHECK_READ_$$r(p0$2, BV32_ADD(SrcOffset$2, Index$2), _abstracted_call_arg_3$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_READ_$$r"} true;
    return;
}

const _WATCHED_VALUE_$$p: bv32;

var _READ_ASYNC_HANDLE_$$p: bv32;

procedure {:inline 1} _LOG_READ_$$p(_P: bool, _offset: bv32, _value: bv32, _async_handle: bv32);
  modifies _READ_HAS_OCCURRED_$$p, _READ_ASYNC_HANDLE_$$p;

implementation {:inline 1} _LOG_READ_$$p(_P: bool, _offset: bv32, _value: bv32, _async_handle: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then true else _READ_HAS_OCCURRED_$$p);
    _READ_ASYNC_HANDLE_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then _async_handle else _READ_ASYNC_HANDLE_$$p);
    return;
}

procedure _CHECK_READ_$$p(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$p);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$p: bool;

procedure {:inline 1} _LOG_WRITE_$$p(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$p, _WRITE_READ_BENIGN_FLAG_$$p;

implementation {:inline 1} _LOG_WRITE_$$p(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then true else _WRITE_HAS_OCCURRED_$$p);
    _WRITE_READ_BENIGN_FLAG_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$p);
    return;
}

procedure _CHECK_WRITE_$$p(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$p(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$p;

implementation {:inline 1} _LOG_ATOMIC_$$p(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$p);
    return;
}

procedure _CHECK_ATOMIC_$$p(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$p;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$p := (if _P && _WRITE_HAS_OCCURRED_$$p && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$p);
    return;
}

const _WATCHED_VALUE_$$q: bv32;

var _READ_ASYNC_HANDLE_$$q: bv32;

procedure {:inline 1} _LOG_READ_$$q(_P: bool, _offset: bv32, _value: bv32, _async_handle: bv32);
  modifies _READ_HAS_OCCURRED_$$q, _READ_ASYNC_HANDLE_$$q;

implementation {:inline 1} _LOG_READ_$$q(_P: bool, _offset: bv32, _value: bv32, _async_handle: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$q := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$q == _value then true else _READ_HAS_OCCURRED_$$q);
    _READ_ASYNC_HANDLE_$$q := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$q == _value then _async_handle else _READ_ASYNC_HANDLE_$$q);
    return;
}

procedure _CHECK_READ_$$q(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$q);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$q: bool;

procedure {:inline 1} _LOG_WRITE_$$q(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$q, _WRITE_READ_BENIGN_FLAG_$$q;

implementation {:inline 1} _LOG_WRITE_$$q(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$q := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$q == _value then true else _WRITE_HAS_OCCURRED_$$q);
    _WRITE_READ_BENIGN_FLAG_$$q := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$q == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$q);
    return;
}

procedure _CHECK_WRITE_$$q(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$q != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$q != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$q(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$q;

implementation {:inline 1} _LOG_ATOMIC_$$q(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$q := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$q);
    return;
}

procedure _CHECK_ATOMIC_$$q(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$q(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$q;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$q(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$q := (if _P && _WRITE_HAS_OCCURRED_$$q && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$q);
    return;
}

const _WATCHED_VALUE_$$r: bv32;

var _READ_ASYNC_HANDLE_$$r: bv32;

procedure {:inline 1} _LOG_READ_$$r(_P: bool, _offset: bv32, _value: bv32, _async_handle: bv32);
  modifies _READ_HAS_OCCURRED_$$r, _READ_ASYNC_HANDLE_$$r;

implementation {:inline 1} _LOG_READ_$$r(_P: bool, _offset: bv32, _value: bv32, _async_handle: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$r := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$r == _value then true else _READ_HAS_OCCURRED_$$r);
    _READ_ASYNC_HANDLE_$$r := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$r == _value then _async_handle else _READ_ASYNC_HANDLE_$$r);
    return;
}

procedure _CHECK_READ_$$r(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$r && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$r);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$r && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$r: bool;

procedure {:inline 1} _LOG_WRITE_$$r(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$r, _WRITE_READ_BENIGN_FLAG_$$r;

implementation {:inline 1} _LOG_WRITE_$$r(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$r := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$r == _value then true else _WRITE_HAS_OCCURRED_$$r);
    _WRITE_READ_BENIGN_FLAG_$$r := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$r == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$r);
    return;
}

procedure _CHECK_WRITE_$$r(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$r && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$r != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$r && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$r != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$r && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$r(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$r;

implementation {:inline 1} _LOG_ATOMIC_$$r(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$r := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$r);
    return;
}

procedure _CHECK_ATOMIC_$$r(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$r && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$r && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$r(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$r;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$r(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$r := (if _P && _WRITE_HAS_OCCURRED_$$r && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$r);
    return;
}

const _WATCHED_VALUE_$$foo.my_p: bv32;

procedure {:inline 1} _LOG_READ_$$foo.my_p(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$foo.my_p;

implementation {:inline 1} _LOG_READ_$$foo.my_p(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$foo.my_p := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_p == _value then true else _READ_HAS_OCCURRED_$$foo.my_p);
    return;
}

procedure _CHECK_READ_$$foo.my_p(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.my_p && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$foo.my_p && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.my_p && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$foo.my_p: bool;

var _WRITE_ASYNC_HANDLE_$$foo.my_p: bv32;

procedure {:inline 1} _LOG_WRITE_$$foo.my_p(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32, _async_handle: bv32);
  modifies _WRITE_HAS_OCCURRED_$$foo.my_p, _WRITE_READ_BENIGN_FLAG_$$foo.my_p, _WRITE_ASYNC_HANDLE_$$foo.my_p;

implementation {:inline 1} _LOG_WRITE_$$foo.my_p(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32, _async_handle: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$foo.my_p := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_p == _value then true else _WRITE_HAS_OCCURRED_$$foo.my_p);
    _WRITE_READ_BENIGN_FLAG_$$foo.my_p := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_p == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$foo.my_p);
    _WRITE_ASYNC_HANDLE_$$foo.my_p := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_p == _value then _async_handle else _WRITE_ASYNC_HANDLE_$$foo.my_p);
    return;
}

procedure _CHECK_WRITE_$$foo.my_p(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.my_p && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_p != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.my_p && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_p != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.my_p && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$foo.my_p(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$foo.my_p;

implementation {:inline 1} _LOG_ATOMIC_$$foo.my_p(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$foo.my_p := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$foo.my_p);
    return;
}

procedure _CHECK_ATOMIC_$$foo.my_p(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.my_p && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.my_p && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.my_p(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$foo.my_p;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.my_p(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$foo.my_p := (if _P && _WRITE_HAS_OCCURRED_$$foo.my_p && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$foo.my_p);
    return;
}

const _WATCHED_VALUE_$$foo.my_q: bv32;

procedure {:inline 1} _LOG_READ_$$foo.my_q(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$foo.my_q;

implementation {:inline 1} _LOG_READ_$$foo.my_q(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$foo.my_q := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_q == _value then true else _READ_HAS_OCCURRED_$$foo.my_q);
    return;
}

procedure _CHECK_READ_$$foo.my_q(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.my_q && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$foo.my_q && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.my_q && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$foo.my_q: bool;

var _WRITE_ASYNC_HANDLE_$$foo.my_q: bv32;

procedure {:inline 1} _LOG_WRITE_$$foo.my_q(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32, _async_handle: bv32);
  modifies _WRITE_HAS_OCCURRED_$$foo.my_q, _WRITE_READ_BENIGN_FLAG_$$foo.my_q, _WRITE_ASYNC_HANDLE_$$foo.my_q;

implementation {:inline 1} _LOG_WRITE_$$foo.my_q(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32, _async_handle: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$foo.my_q := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_q == _value then true else _WRITE_HAS_OCCURRED_$$foo.my_q);
    _WRITE_READ_BENIGN_FLAG_$$foo.my_q := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_q == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$foo.my_q);
    _WRITE_ASYNC_HANDLE_$$foo.my_q := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_q == _value then _async_handle else _WRITE_ASYNC_HANDLE_$$foo.my_q);
    return;
}

procedure _CHECK_WRITE_$$foo.my_q(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.my_q && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_q != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.my_q && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_q != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.my_q && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$foo.my_q(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$foo.my_q;

implementation {:inline 1} _LOG_ATOMIC_$$foo.my_q(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$foo.my_q := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$foo.my_q);
    return;
}

procedure _CHECK_ATOMIC_$$foo.my_q(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.my_q && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.my_q && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.my_q(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$foo.my_q;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.my_q(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$foo.my_q := (if _P && _WRITE_HAS_OCCURRED_$$foo.my_q && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$foo.my_q);
    return;
}

const _WATCHED_VALUE_$$foo.my_r: bv32;

procedure {:inline 1} _LOG_READ_$$foo.my_r(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$foo.my_r;

implementation {:inline 1} _LOG_READ_$$foo.my_r(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$foo.my_r := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_r == _value then true else _READ_HAS_OCCURRED_$$foo.my_r);
    return;
}

procedure _CHECK_READ_$$foo.my_r(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.my_r && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$foo.my_r && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.my_r && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

var _WRITE_READ_BENIGN_FLAG_$$foo.my_r: bool;

var _WRITE_ASYNC_HANDLE_$$foo.my_r: bv32;

procedure {:inline 1} _LOG_WRITE_$$foo.my_r(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32, _async_handle: bv32);
  modifies _WRITE_HAS_OCCURRED_$$foo.my_r, _WRITE_READ_BENIGN_FLAG_$$foo.my_r, _WRITE_ASYNC_HANDLE_$$foo.my_r;

implementation {:inline 1} _LOG_WRITE_$$foo.my_r(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32, _async_handle: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$foo.my_r := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_r == _value then true else _WRITE_HAS_OCCURRED_$$foo.my_r);
    _WRITE_READ_BENIGN_FLAG_$$foo.my_r := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_r == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$foo.my_r);
    _WRITE_ASYNC_HANDLE_$$foo.my_r := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_r == _value then _async_handle else _WRITE_ASYNC_HANDLE_$$foo.my_r);
    return;
}

procedure _CHECK_WRITE_$$foo.my_r(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.my_r && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_r != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.my_r && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$foo.my_r != _value && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$foo.my_r && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _LOG_ATOMIC_$$foo.my_r(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$foo.my_r;

implementation {:inline 1} _LOG_ATOMIC_$$foo.my_r(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$foo.my_r := (if _P && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2 && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$foo.my_r);
    return;
}

procedure _CHECK_ATOMIC_$$foo.my_r(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$foo.my_r && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);
  requires !(_P && _READ_HAS_OCCURRED_$$foo.my_r && _WATCHED_OFFSET == _offset && group_id_x$1 == group_id_x$2 && group_id_y$1 == group_id_y$2 && group_id_z$1 == group_id_z$2);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.my_r(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$foo.my_r;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$foo.my_r(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$foo.my_r := (if _P && _WRITE_HAS_OCCURRED_$$foo.my_r && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$foo.my_r);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
