//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "p"} {:global} $$p: [bv32]bv32;

axiom {:array_info "$$p"} {:global} {:elem_width 32} {:source_name "p"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$p: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$p: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$p: bool;

const $arrayId$$p: arrayId;

axiom $arrayId$$p == 1bv3;

var {:source_name "q"} {:global} $$q: [bv32]bv32;

axiom {:array_info "$$q"} {:global} {:elem_width 32} {:source_name "q"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$q: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$q: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$q: bool;

const $arrayId$$q: arrayId;

axiom $arrayId$$q == 2bv3;

var {:source_name "r"} {:global} $$r: [bv32]bv32;

axiom {:array_info "$$r"} {:global} {:elem_width 32} {:source_name "r"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$r: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$r: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$r: bool;

const $arrayId$$r: arrayId;

axiom $arrayId$$r == 3bv3;

var {:source_name "s"} {:global} $$s: [bv32]bv32;

axiom {:array_info "$$s"} {:global} {:elem_width 32} {:source_name "s"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$s: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$s: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$s: bool;

const $arrayId$$s: arrayId;

axiom $arrayId$$s == 4bv3;

var {:source_name "t"} {:global} $$t: [bv32]bv32;

axiom {:array_info "$$t"} {:global} {:elem_width 32} {:source_name "t"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$t: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$t: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$t: bool;

const $arrayId$$t: arrayId;

axiom $arrayId$$t == 5bv3;

var {:source_name "u"} {:global} $$u: [bv32]bv32;

axiom {:array_info "$$u"} {:global} {:elem_width 32} {:source_name "u"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$u: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$u: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$u: bool;

const $arrayId$$u: arrayId;

axiom $arrayId$$u == 6bv3;

type ptr = bv32;

type arrayId = bv3;

function {:inline true} MKPTR(base: arrayId, offset: bv32) : ptr
{
  base ++ offset[29:0]
}

function {:inline true} base#MKPTR(p: ptr) : arrayId
{
  p[32:29]
}

function {:inline true} offset#MKPTR(p: ptr) : bv32
{
  0bv3 ++ p[29:0]
}

const $arrayId$$null$: arrayId;

axiom $arrayId$$null$ == 0bv3;

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

function UI32_TO_FP32(bv32) : bv32;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

procedure {:source_name "foo"} ULTIMATE.start($x: bv32);
  requires !_READ_HAS_OCCURRED_$$p && !_WRITE_HAS_OCCURRED_$$p && !_ATOMIC_HAS_OCCURRED_$$p;
  requires !_READ_HAS_OCCURRED_$$q && !_WRITE_HAS_OCCURRED_$$q && !_ATOMIC_HAS_OCCURRED_$$q;
  requires !_READ_HAS_OCCURRED_$$r && !_WRITE_HAS_OCCURRED_$$r && !_ATOMIC_HAS_OCCURRED_$$r;
  requires !_READ_HAS_OCCURRED_$$s && !_WRITE_HAS_OCCURRED_$$s && !_ATOMIC_HAS_OCCURRED_$$s;
  requires !_READ_HAS_OCCURRED_$$t && !_WRITE_HAS_OCCURRED_$$t && !_ATOMIC_HAS_OCCURRED_$$t;
  requires !_READ_HAS_OCCURRED_$$u && !_WRITE_HAS_OCCURRED_$$u && !_ATOMIC_HAS_OCCURRED_$$u;
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
  modifies _WRITE_HAS_OCCURRED_$$r, _WRITE_READ_BENIGN_FLAG_$$r, _WRITE_READ_BENIGN_FLAG_$$r, _WRITE_HAS_OCCURRED_$$s, _WRITE_READ_BENIGN_FLAG_$$s, _WRITE_READ_BENIGN_FLAG_$$s, _WRITE_HAS_OCCURRED_$$t, _WRITE_READ_BENIGN_FLAG_$$t, _WRITE_READ_BENIGN_FLAG_$$t, _WRITE_HAS_OCCURRED_$$u, _WRITE_READ_BENIGN_FLAG_$$u, _WRITE_READ_BENIGN_FLAG_$$u, _WRITE_HAS_OCCURRED_$$p, _WRITE_READ_BENIGN_FLAG_$$p, _WRITE_READ_BENIGN_FLAG_$$p, _WRITE_HAS_OCCURRED_$$q, _WRITE_READ_BENIGN_FLAG_$$q, _WRITE_READ_BENIGN_FLAG_$$q;

implementation {:source_name "foo"} ULTIMATE.start($x: bv32)
{
  var $temp.0: ptr;
  var v0: bool;

  $entry:
    v0 := BV32_SGT($x, 4bv32);
    goto $truebb, $falsebb;

  $falsebb:
    assume {:partition} !v0;
    $temp.0 := MKPTR($arrayId$$q, 0bv32);
    goto $if.end;

  $if.end:
    goto anon4_Then, anon4_Else;

  anon4_Else:
    assume {:partition} base#MKPTR($temp.0) != $arrayId$$q;
    goto anon5_Then, anon5_Else;

  anon5_Else:
    assume {:partition} base#MKPTR($temp.0) != $arrayId$$p;
    assert {:bad_pointer_access} {:sourceloc_num 5} {:thread 1} false;
    goto anon3;

  anon3:
    call _LOG_WRITE_$$r(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)), $$r[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$r(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 6} true;
    call _CHECK_WRITE_$$r(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$r"} true;
    $$r[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1));
    $$r[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    call _LOG_WRITE_$$s(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)), $$s[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$s(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 7} true;
    call _CHECK_WRITE_$$s(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$s"} true;
    $$s[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1));
    $$s[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    call _LOG_WRITE_$$t(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)), $$t[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$t(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 8} true;
    call _CHECK_WRITE_$$t(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$t"} true;
    $$t[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1));
    $$t[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    call _LOG_WRITE_$$t(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)), $$t[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$t(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 9} true;
    call _CHECK_WRITE_$$t(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$t"} true;
    $$t[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1));
    $$t[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    call _LOG_WRITE_$$u(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)), $$u[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$u(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_4"} {:captureState "check_state_4"} {:sourceloc} {:sourceloc_num 10} true;
    call _CHECK_WRITE_$$u(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$u"} true;
    $$u[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1));
    $$u[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    call _LOG_WRITE_$$s(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)), $$s[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$s(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_5"} {:captureState "check_state_5"} {:sourceloc} {:sourceloc_num 11} true;
    call _CHECK_WRITE_$$s(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$s"} true;
    $$s[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1));
    $$s[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    call _LOG_WRITE_$$r(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)), $$r[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$r(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_6"} {:captureState "check_state_6"} {:sourceloc} {:sourceloc_num 12} true;
    call _CHECK_WRITE_$$r(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$r"} true;
    $$r[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1));
    $$r[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    call _LOG_WRITE_$$r(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)), $$r[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$r(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_7"} {:captureState "check_state_7"} {:sourceloc} {:sourceloc_num 13} true;
    call _CHECK_WRITE_$$r(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$r"} true;
    $$r[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1));
    $$r[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    call _LOG_WRITE_$$t(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)), $$t[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$t(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_8"} {:captureState "check_state_8"} {:sourceloc} {:sourceloc_num 14} true;
    call _CHECK_WRITE_$$t(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$t"} true;
    $$t[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1));
    $$t[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    call _LOG_WRITE_$$t(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)), $$t[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$t(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_9"} {:captureState "check_state_9"} {:sourceloc} {:sourceloc_num 15} true;
    call _CHECK_WRITE_$$t(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$t"} true;
    $$t[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1));
    $$t[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    call _LOG_WRITE_$$s(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)), $$s[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$s(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_10"} {:captureState "check_state_10"} {:sourceloc} {:sourceloc_num 16} true;
    call _CHECK_WRITE_$$s(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$s"} true;
    $$s[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1));
    $$s[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    call _LOG_WRITE_$$t(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)), $$t[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$t(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_11"} {:captureState "check_state_11"} {:sourceloc} {:sourceloc_num 17} true;
    call _CHECK_WRITE_$$t(true, BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$t"} true;
    $$t[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1));
    $$t[BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32)] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    return;

  anon5_Then:
    assume {:partition} base#MKPTR($temp.0) == $arrayId$$p;
    call _LOG_WRITE_$$p(true, BV32_ADD(offset#MKPTR($temp.0), BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)), $$p[BV32_ADD(offset#MKPTR($temp.0), BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1))]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$p(true, BV32_ADD(offset#MKPTR($temp.0), BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)));
    assume {:do_not_predicate} {:check_id "check_state_12"} {:captureState "check_state_12"} {:sourceloc} {:sourceloc_num 4} true;
    call _CHECK_WRITE_$$p(true, BV32_ADD(offset#MKPTR($temp.0), BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$p"} true;
    $$p[BV32_ADD(offset#MKPTR($temp.0), BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1))] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1));
    $$p[BV32_ADD(offset#MKPTR($temp.0), BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2))] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    goto anon3;

  anon4_Then:
    assume {:partition} base#MKPTR($temp.0) == $arrayId$$q;
    call _LOG_WRITE_$$q(true, BV32_ADD(offset#MKPTR($temp.0), BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1)), $$q[BV32_ADD(offset#MKPTR($temp.0), BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1))]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$q(true, BV32_ADD(offset#MKPTR($temp.0), BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)));
    assume {:do_not_predicate} {:check_id "check_state_13"} {:captureState "check_state_13"} {:sourceloc} {:sourceloc_num 3} true;
    call _CHECK_WRITE_$$q(true, BV32_ADD(offset#MKPTR($temp.0), BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)), UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2)));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$q"} true;
    $$q[BV32_ADD(offset#MKPTR($temp.0), BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1))] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1));
    $$q[BV32_ADD(offset#MKPTR($temp.0), BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2))] := UI32_TO_FP32(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2));
    goto anon3;

  $truebb:
    assume {:partition} v0;
    $temp.0 := MKPTR($arrayId$$p, 0bv32);
    goto $if.end;
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

const {:local_id_y} local_id_y$1: bv32;

const {:local_id_y} local_id_y$2: bv32;

const {:local_id_z} local_id_z$1: bv32;

const {:local_id_z} local_id_z$2: bv32;

const {:group_id_y} group_id_y$1: bv32;

const {:group_id_y} group_id_y$2: bv32;

const {:group_id_z} group_id_z$1: bv32;

const {:group_id_z} group_id_z$2: bv32;

const _WATCHED_VALUE_$$p: bv32;

procedure {:inline 1} _LOG_READ_$$p(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$p;

implementation {:inline 1} _LOG_READ_$$p(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$p := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p == _value then true else _READ_HAS_OCCURRED_$$p);
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

procedure {:inline 1} _LOG_READ_$$q(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$q;

implementation {:inline 1} _LOG_READ_$$q(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$q := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$q == _value then true else _READ_HAS_OCCURRED_$$q);
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

procedure {:inline 1} _LOG_READ_$$r(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$r;

implementation {:inline 1} _LOG_READ_$$r(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$r := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$r == _value then true else _READ_HAS_OCCURRED_$$r);
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

const _WATCHED_VALUE_$$s: bv32;

procedure {:inline 1} _LOG_READ_$$s(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$s;

implementation {:inline 1} _LOG_READ_$$s(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$s := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$s == _value then true else _READ_HAS_OCCURRED_$$s);
    return;
}

procedure _CHECK_READ_$$s(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$s && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$s);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$s && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$s: bool;

procedure {:inline 1} _LOG_WRITE_$$s(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$s, _WRITE_READ_BENIGN_FLAG_$$s;

implementation {:inline 1} _LOG_WRITE_$$s(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$s := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$s == _value then true else _WRITE_HAS_OCCURRED_$$s);
    _WRITE_READ_BENIGN_FLAG_$$s := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$s == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$s);
    return;
}

procedure _CHECK_WRITE_$$s(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$s && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$s != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$s && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$s != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$s && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$s(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$s;

implementation {:inline 1} _LOG_ATOMIC_$$s(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$s := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$s);
    return;
}

procedure _CHECK_ATOMIC_$$s(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$s && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$s && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$s(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$s;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$s(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$s := (if _P && _WRITE_HAS_OCCURRED_$$s && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$s);
    return;
}

const _WATCHED_VALUE_$$t: bv32;

procedure {:inline 1} _LOG_READ_$$t(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$t;

implementation {:inline 1} _LOG_READ_$$t(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$t := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$t == _value then true else _READ_HAS_OCCURRED_$$t);
    return;
}

procedure _CHECK_READ_$$t(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$t && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$t);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$t && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$t: bool;

procedure {:inline 1} _LOG_WRITE_$$t(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$t, _WRITE_READ_BENIGN_FLAG_$$t;

implementation {:inline 1} _LOG_WRITE_$$t(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$t := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$t == _value then true else _WRITE_HAS_OCCURRED_$$t);
    _WRITE_READ_BENIGN_FLAG_$$t := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$t == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$t);
    return;
}

procedure _CHECK_WRITE_$$t(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$t && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$t != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$t && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$t != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$t && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$t(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$t;

implementation {:inline 1} _LOG_ATOMIC_$$t(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$t := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$t);
    return;
}

procedure _CHECK_ATOMIC_$$t(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$t && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$t && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$t(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$t;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$t(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$t := (if _P && _WRITE_HAS_OCCURRED_$$t && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$t);
    return;
}

const _WATCHED_VALUE_$$u: bv32;

procedure {:inline 1} _LOG_READ_$$u(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$u;

implementation {:inline 1} _LOG_READ_$$u(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$u := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$u == _value then true else _READ_HAS_OCCURRED_$$u);
    return;
}

procedure _CHECK_READ_$$u(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$u && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$u);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$u && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$u: bool;

procedure {:inline 1} _LOG_WRITE_$$u(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$u, _WRITE_READ_BENIGN_FLAG_$$u;

implementation {:inline 1} _LOG_WRITE_$$u(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$u := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$u == _value then true else _WRITE_HAS_OCCURRED_$$u);
    _WRITE_READ_BENIGN_FLAG_$$u := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$u == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$u);
    return;
}

procedure _CHECK_WRITE_$$u(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$u && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$u != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$u && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$u != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$u && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$u(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$u;

implementation {:inline 1} _LOG_ATOMIC_$$u(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$u := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$u);
    return;
}

procedure _CHECK_ATOMIC_$$u(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$u && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$u && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$u(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$u;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$u(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$u := (if _P && _WRITE_HAS_OCCURRED_$$u && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$u);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
