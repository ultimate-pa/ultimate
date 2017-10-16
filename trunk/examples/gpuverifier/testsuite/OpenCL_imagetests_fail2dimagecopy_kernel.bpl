//#Unsafe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

var {:source_name "dest"} {:global} $$dest: [bv32]bv32;

axiom {:array_info "$$dest"} {:global} {:elem_width 32} {:source_name "dest"} {:source_elem_width 128} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$dest: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$dest: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$dest: bool;

const $arrayId$$dest: arrayId;

axiom $arrayId$$dest == 1bv2;

axiom {:array_info "$$src"} {:global} {:elem_width 32} {:source_name "src"} {:source_elem_width 128} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$src: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$src: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 128} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$src: bool;

const $arrayId$$src: arrayId;

axiom $arrayId$$src == 2bv2;

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

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;

procedure {:source_name "k"} ULTIMATE.start();
  requires !_READ_HAS_OCCURRED_$$dest && !_WRITE_HAS_OCCURRED_$$dest && !_ATOMIC_HAS_OCCURRED_$$dest;
  requires !_READ_HAS_OCCURRED_$$src && !_WRITE_HAS_OCCURRED_$$src && !_ATOMIC_HAS_OCCURRED_$$src;
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
  modifies _WRITE_HAS_OCCURRED_$$dest, _WRITE_READ_BENIGN_FLAG_$$dest, _WRITE_READ_BENIGN_FLAG_$$dest;

implementation {:source_name "k"} ULTIMATE.start()
{
  var $cond5.i$1: bv32;
  var $cond5.i$2: bv32;
  var $cond.i$1: bv32;
  var $cond.i$2: bv32;
  var $cond15.i$1: bv32;
  var $cond15.i$2: bv32;
  var $cond13.i$1: bv32;
  var $cond13.i$2: bv32;
  var v0$1: ptr;
  var v0$2: ptr;
  var v1$1: bv32;
  var v1$2: bv32;
  var v2$1: bv32;
  var v2$2: bv32;
  var v3$1: bool;
  var v3$2: bool;
  var v4$1: bool;
  var v4$2: bool;
  var v5$1: bool;
  var v5$2: bool;
  var v6$1: bool;
  var v6$2: bool;
  var v7$1: bv32;
  var v7$2: bv32;
  var v8$1: bv32;
  var v8$2: bv32;
  var v9$1: bv32;
  var v9$2: bv32;
  var v10$1: bv32;
  var v10$2: bv32;
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

  $entry:
    call v0$1, v0$2 := $__translate_sampler_initializer(2bv32);
    assume {:captureState "call_return_state_0"} {:procedureName "$__translate_sampler_initializer"} true;
    v1$1 := BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1);
    v1$2 := BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2);
    v2$1 := BV32_ADD(BV32_MUL(group_id_y$1, group_size_y), local_id_y$1);
    v2$2 := BV32_ADD(BV32_MUL(group_id_y$2, group_size_y), local_id_y$2);
    v3$1 := BV32_SLT(v1$1, 0bv32);
    v3$2 := BV32_SLT(v1$2, 0bv32);
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
    p0$1 := (if v3$1 then v3$1 else p0$1);
    p0$2 := (if v3$2 then v3$2 else p0$2);
    p1$1 := (if !v3$1 then !v3$1 else p1$1);
    p1$2 := (if !v3$2 then !v3$2 else p1$2);
    $cond5.i$1 := (if p0$1 then 0bv32 else $cond5.i$1);
    $cond5.i$2 := (if p0$2 then 0bv32 else $cond5.i$2);
    v4$1 := (if p1$1 then BV32_SGE(v1$1, 8192bv32) else v4$1);
    v4$2 := (if p1$2 then BV32_SGE(v1$2, 8192bv32) else v4$2);
    p2$1 := (if p1$1 && v4$1 then v4$1 else p2$1);
    p2$2 := (if p1$2 && v4$2 then v4$2 else p2$2);
    p3$1 := (if p1$1 && !v4$1 then !v4$1 else p3$1);
    p3$2 := (if p1$2 && !v4$2 then !v4$2 else p3$2);
    $cond.i$1 := (if p2$1 then 8191bv32 else $cond.i$1);
    $cond.i$2 := (if p2$2 then 8191bv32 else $cond.i$2);
    $cond.i$1 := (if p3$1 then v1$1 else $cond.i$1);
    $cond.i$2 := (if p3$2 then v1$2 else $cond.i$2);
    $cond5.i$1 := (if p1$1 then $cond.i$1 else $cond5.i$1);
    $cond5.i$2 := (if p1$2 then $cond.i$2 else $cond5.i$2);
    v5$1 := BV32_SLT(v2$1, 0bv32);
    v5$2 := BV32_SLT(v2$2, 0bv32);
    p4$1 := (if v5$1 then v5$1 else p4$1);
    p4$2 := (if v5$2 then v5$2 else p4$2);
    p5$1 := (if !v5$1 then !v5$1 else p5$1);
    p5$2 := (if !v5$2 then !v5$2 else p5$2);
    $cond15.i$1 := (if p4$1 then 0bv32 else $cond15.i$1);
    $cond15.i$2 := (if p4$2 then 0bv32 else $cond15.i$2);
    v6$1 := (if p5$1 then BV32_SGE(v2$1, 8192bv32) else v6$1);
    v6$2 := (if p5$2 then BV32_SGE(v2$2, 8192bv32) else v6$2);
    p6$1 := (if p5$1 && v6$1 then v6$1 else p6$1);
    p6$2 := (if p5$2 && v6$2 then v6$2 else p6$2);
    p7$1 := (if p5$1 && !v6$1 then !v6$1 else p7$1);
    p7$2 := (if p5$2 && !v6$2 then !v6$2 else p7$2);
    $cond13.i$1 := (if p6$1 then 8191bv32 else $cond13.i$1);
    $cond13.i$2 := (if p6$2 then 8191bv32 else $cond13.i$2);
    $cond13.i$1 := (if p7$1 then v2$1 else $cond13.i$1);
    $cond13.i$2 := (if p7$2 then v2$2 else $cond13.i$2);
    $cond15.i$1 := (if p5$1 then $cond13.i$1 else $cond15.i$1);
    $cond15.i$2 := (if p5$2 then $cond13.i$2 else $cond15.i$2);
    havoc v7$1, v7$2;
    havoc v8$1, v8$2;
    havoc v9$1, v9$2;
    havoc v10$1, v10$2;
    call _LOG_WRITE_$$dest(true, BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$1, group_size_y), local_id_y$1), 8192bv32), 4bv32), v7$1, $$dest[BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$1, group_size_y), local_id_y$1), 8192bv32), 4bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$dest(true, BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$2, group_size_y), local_id_y$2), 8192bv32), 4bv32));
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 18} true;
    call _CHECK_WRITE_$$dest(true, BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$2, group_size_y), local_id_y$2), 8192bv32), 4bv32), v7$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$dest"} true;
    $$dest[BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$1, group_size_y), local_id_y$1), 8192bv32), 4bv32)] := v7$1;
    $$dest[BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$2, group_size_y), local_id_y$2), 8192bv32), 4bv32)] := v7$2;
    call _LOG_WRITE_$$dest(true, BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$1, group_size_y), local_id_y$1), 8192bv32), 4bv32), 1bv32), v8$1, $$dest[BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$1, group_size_y), local_id_y$1), 8192bv32), 4bv32), 1bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$dest(true, BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$2, group_size_y), local_id_y$2), 8192bv32), 4bv32), 1bv32));
    assume {:do_not_predicate} {:check_id "check_state_1"} {:captureState "check_state_1"} {:sourceloc} {:sourceloc_num 19} true;
    call _CHECK_WRITE_$$dest(true, BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$2, group_size_y), local_id_y$2), 8192bv32), 4bv32), 1bv32), v8$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$dest"} true;
    $$dest[BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$1, group_size_y), local_id_y$1), 8192bv32), 4bv32), 1bv32)] := v8$1;
    $$dest[BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$2, group_size_y), local_id_y$2), 8192bv32), 4bv32), 1bv32)] := v8$2;
    call _LOG_WRITE_$$dest(true, BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$1, group_size_y), local_id_y$1), 8192bv32), 4bv32), 2bv32), v9$1, $$dest[BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$1, group_size_y), local_id_y$1), 8192bv32), 4bv32), 2bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$dest(true, BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$2, group_size_y), local_id_y$2), 8192bv32), 4bv32), 2bv32));
    assume {:do_not_predicate} {:check_id "check_state_2"} {:captureState "check_state_2"} {:sourceloc} {:sourceloc_num 20} true;
    call _CHECK_WRITE_$$dest(true, BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$2, group_size_y), local_id_y$2), 8192bv32), 4bv32), 2bv32), v9$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$dest"} true;
    $$dest[BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$1, group_size_y), local_id_y$1), 8192bv32), 4bv32), 2bv32)] := v9$1;
    $$dest[BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$2, group_size_y), local_id_y$2), 8192bv32), 4bv32), 2bv32)] := v9$2;
    call _LOG_WRITE_$$dest(true, BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$1, group_size_y), local_id_y$1), 8192bv32), 4bv32), 3bv32), v10$1, $$dest[BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$1, group_size_y), local_id_y$1), 8192bv32), 4bv32), 3bv32)]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$dest(true, BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$2, group_size_y), local_id_y$2), 8192bv32), 4bv32), 3bv32));
    assume {:do_not_predicate} {:check_id "check_state_3"} {:captureState "check_state_3"} {:sourceloc} {:sourceloc_num 21} true;
    call _CHECK_WRITE_$$dest(true, BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$2, group_size_y), local_id_y$2), 8192bv32), 4bv32), 3bv32), v10$2);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$dest"} true;
    $$dest[BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$1, group_size_y), local_id_y$1), 8192bv32), 4bv32), 3bv32)] := v10$1;
    $$dest[BV32_ADD(BV32_MUL(BV32_MUL(BV32_ADD(BV32_MUL(group_id_y$2, group_size_y), local_id_y$2), 8192bv32), 4bv32), 3bv32)] := v10$2;
    return;
}

procedure {:source_name "__translate_sampler_initializer"} $__translate_sampler_initializer($0: bv32) returns ($ret$1: ptr, $ret$2: ptr);
  requires $0 == 2bv32;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 8bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_y == 8bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 8bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 8bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_x == 0bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_y == 0bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if global_offset_z == 0bv32 then 1bv1 else 0bv1) != 0bv1;

const {:local_id_z} local_id_z$1: bv32;

const {:local_id_z} local_id_z$2: bv32;

const {:group_id_z} group_id_z$1: bv32;

const {:group_id_z} group_id_z$2: bv32;

const _WATCHED_VALUE_$$dest: bv32;

procedure {:inline 1} _LOG_READ_$$dest(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$dest;

implementation {:inline 1} _LOG_READ_$$dest(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$dest := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$dest == _value then true else _READ_HAS_OCCURRED_$$dest);
    return;
}

procedure _CHECK_READ_$$dest(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$dest && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$dest);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$dest && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$dest: bool;

procedure {:inline 1} _LOG_WRITE_$$dest(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$dest, _WRITE_READ_BENIGN_FLAG_$$dest;

implementation {:inline 1} _LOG_WRITE_$$dest(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$dest := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$dest == _value then true else _WRITE_HAS_OCCURRED_$$dest);
    _WRITE_READ_BENIGN_FLAG_$$dest := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$dest == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$dest);
    return;
}

procedure _CHECK_WRITE_$$dest(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$dest && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$dest != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$dest && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$dest != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$dest && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$dest(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$dest;

implementation {:inline 1} _LOG_ATOMIC_$$dest(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$dest := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$dest);
    return;
}

procedure _CHECK_ATOMIC_$$dest(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$dest && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$dest && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$dest(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$dest;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$dest(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$dest := (if _P && _WRITE_HAS_OCCURRED_$$dest && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$dest);
    return;
}

const _WATCHED_VALUE_$$src: bv32;

procedure {:inline 1} _LOG_READ_$$src(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$src;

implementation {:inline 1} _LOG_READ_$$src(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$src := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$src == _value then true else _READ_HAS_OCCURRED_$$src);
    return;
}

procedure _CHECK_READ_$$src(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$src && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$src);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$src && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$src: bool;

procedure {:inline 1} _LOG_WRITE_$$src(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$src, _WRITE_READ_BENIGN_FLAG_$$src;

implementation {:inline 1} _LOG_WRITE_$$src(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$src := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$src == _value then true else _WRITE_HAS_OCCURRED_$$src);
    _WRITE_READ_BENIGN_FLAG_$$src := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$src == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$src);
    return;
}

procedure _CHECK_WRITE_$$src(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$src && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$src != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$src && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$src != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$src && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$src(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$src;

implementation {:inline 1} _LOG_ATOMIC_$$src(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$src := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$src);
    return;
}

procedure _CHECK_ATOMIC_$$src(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$src && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$src && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$src(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$src;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$src(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$src := (if _P && _WRITE_HAS_OCCURRED_$$src && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$src);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;
