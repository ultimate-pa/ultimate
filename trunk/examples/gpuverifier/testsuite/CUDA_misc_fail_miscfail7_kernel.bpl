//#Unsafe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP8(x: [bv32]bv8, y: bv32) returns (z$1: bv8, A$1: [bv32]bv8, z$2: bv8, A$2: [bv32]bv8);

var {:source_name "H"} {:global} $$H: [bv32]bv8;

axiom {:array_info "$$H"} {:global} {:elem_width 8} {:source_name "H"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$H: bool;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$H: bool;

var {:race_checking} {:global} {:elem_width 8} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$H: bool;

const $arrayId$$H: arrayId;

axiom $arrayId$$H == 1bv2;

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

const {:group_size_x} group_size_x: bv32;

const {:group_size_y} group_size_y: bv32;

const {:group_size_z} group_size_z: bv32;

const {:local_id_x} local_id_x$1: bv32;

const {:local_id_x} local_id_x$2: bv32;

const {:num_groups_x} num_groups_x: bv32;

const {:num_groups_y} num_groups_y: bv32;

const {:num_groups_z} num_groups_z: bv32;

function BV32_TO_PTR(bv32) : ptr;

function PTR_TO_BV32(ptr) : bv32;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

procedure {:source_name "foo"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$H && !_WRITE_HAS_OCCURRED_$$H && !_ATOMIC_HAS_OCCURRED_$$H;
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
  modifies _WRITE_HAS_OCCURRED_$$H, _WRITE_READ_BENIGN_FLAG_$$H, _WRITE_READ_BENIGN_FLAG_$$H;

implementation {:source_name "foo"} ULTIMATE.start()
{
  var v0: ptr;

  $entry:
    v0 := BV32_TO_PTR(BV32_ADD(PTR_TO_BV32(MKPTR($arrayId$$H, 0bv32)), 4bv32));
    goto anon12_Then, anon12_Else;

  anon12_Else:
    assume {:partition} base#MKPTR(v0) != $arrayId$$H;
    assert {:bad_pointer_access} {:sourceloc_num 2} {:thread 1} false;
    goto anon2;

  anon2:
    goto anon13_Then, anon13_Else;

  anon13_Else:
    assume {:partition} base#MKPTR(v0) != $arrayId$$H;
    assert {:bad_pointer_access} {:sourceloc_num 4} {:thread 1} false;
    goto anon5;

  anon5:
    goto anon14_Then, anon14_Else;

  anon14_Else:
    assume {:partition} base#MKPTR(v0) != $arrayId$$H;
    assert {:bad_pointer_access} {:sourceloc_num 6} {:thread 1} false;
    goto anon8;

  anon8:
    goto anon15_Then, anon15_Else;

  anon15_Else:
    assume {:partition} base#MKPTR(v0) != $arrayId$$H;
    assert {:bad_pointer_access} {:sourceloc_num 8} {:thread 1} false;
    goto anon11;

  anon11:
    return;

  anon15_Then:
    assume {:partition} base#MKPTR(v0) == $arrayId$$H;
    call _LOG_WRITE_$$H(true, BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$1, 4bv32)), 3bv32), local_id_x$1[32:24], $$H[BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$1, 4bv32)), 3bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$H(true, BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$2, 4bv32)), 3bv32));
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 7} true;
    call _CHECK_WRITE_$$H(true, BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$2, 4bv32)), 3bv32), local_id_x$2[32:24]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$H"} true;
    $$H[BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$1, 4bv32)), 3bv32)] := local_id_x$1[32:24];
    $$H[BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$2, 4bv32)), 3bv32)] := local_id_x$2[32:24];
    goto anon11;

  anon14_Then:
    assume {:partition} base#MKPTR(v0) == $arrayId$$H;
    call _LOG_WRITE_$$H(true, BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$1, 4bv32)), 2bv32), local_id_x$1[24:16], $$H[BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$1, 4bv32)), 2bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$H(true, BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$2, 4bv32)), 2bv32));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 5} true;
    call _CHECK_WRITE_$$H(true, BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$2, 4bv32)), 2bv32), local_id_x$2[24:16]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$H"} true;
    $$H[BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$1, 4bv32)), 2bv32)] := local_id_x$1[24:16];
    $$H[BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$2, 4bv32)), 2bv32)] := local_id_x$2[24:16];
    goto anon8;

  anon13_Then:
    assume {:partition} base#MKPTR(v0) == $arrayId$$H;
    call _LOG_WRITE_$$H(true, BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$1, 4bv32)), 1bv32), local_id_x$1[16:8], $$H[BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$1, 4bv32)), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$H(true, BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$2, 4bv32)), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 3} true;
    call _CHECK_WRITE_$$H(true, BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$2, 4bv32)), 1bv32), local_id_x$2[16:8]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$H"} true;
    $$H[BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$1, 4bv32)), 1bv32)] := local_id_x$1[16:8];
    $$H[BV32_ADD(BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$2, 4bv32)), 1bv32)] := local_id_x$2[16:8];
    goto anon5;

  anon12_Then:
    assume {:partition} base#MKPTR(v0) == $arrayId$$H;
    call _LOG_WRITE_$$H(true, BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$1, 4bv32)), local_id_x$1[8:0], $$H[BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$1, 4bv32))]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$H(true, BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$2, 4bv32)));
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 1} true;
    call _CHECK_WRITE_$$H(true, BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$2, 4bv32)), local_id_x$2[8:0]);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$H"} true;
    $$H[BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$1, 4bv32))] := local_id_x$1[8:0];
    $$H[BV32_ADD(BV32_ADD(offset#MKPTR(v0), 4294967292bv32), BV32_MUL(local_id_x$2, 4bv32))] := local_id_x$2[8:0];
    goto anon2;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 1024bv32 then 1bv1 else 0bv1) != 0bv1;

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

const _WATCHED_VALUE_$$H: bv8;

procedure {:inline 1} _LOG_READ_$$H(_P: bool, _offset: bv32, _value: bv8);
  modifies _READ_HAS_OCCURRED_$$H;

implementation {:inline 1} _LOG_READ_$$H(_P: bool, _offset: bv32, _value: bv8)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$H := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$H == _value then true else _READ_HAS_OCCURRED_$$H);
    return;
}

procedure _CHECK_READ_$$H(_P: bool, _offset: bv32, _value: bv8);
  requires !(_P && _WRITE_HAS_OCCURRED_$$H && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$H);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$H && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$H: bool;

procedure {:inline 1} _LOG_WRITE_$$H(_P: bool, _offset: bv32, _value: bv8, _value_old: bv8);
  modifies _WRITE_HAS_OCCURRED_$$H, _WRITE_READ_BENIGN_FLAG_$$H;

implementation {:inline 1} _LOG_WRITE_$$H(_P: bool, _offset: bv32, _value: bv8, _value_old: bv8)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$H := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$H == _value then true else _WRITE_HAS_OCCURRED_$$H);
    _WRITE_READ_BENIGN_FLAG_$$H := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$H == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$H);
    return;
}

procedure _CHECK_WRITE_$$H(_P: bool, _offset: bv32, _value: bv8);
  requires !(_P && _WRITE_HAS_OCCURRED_$$H && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$H != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$H && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$H != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$H && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$H(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$H;

implementation {:inline 1} _LOG_ATOMIC_$$H(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$H := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$H);
    return;
}

procedure _CHECK_ATOMIC_$$H(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$H && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$H && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$H(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$H;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$H(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$H := (if _P && _WRITE_HAS_OCCURRED_$$H && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$H);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
