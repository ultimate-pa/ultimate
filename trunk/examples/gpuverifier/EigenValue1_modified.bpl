type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);



var {:source_name "numEigenIntervals"} {:global} $$numEigenIntervals: [bv32]bv32;

axiom {:array_info "$$numEigenIntervals"} {:global} {:elem_width 32} {:source_name "numEigenIntervals"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$numEigenIntervals: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$numEigenIntervals: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$numEigenIntervals: bool;

axiom {:array_info "$$eigenIntervals"} {:global} {:elem_width 32} {:source_name "eigenIntervals"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$eigenIntervals: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$eigenIntervals: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$eigenIntervals: bool;

axiom {:array_info "$$diagonal"} {:global} {:elem_width 32} {:source_name "diagonal"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$diagonal: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$diagonal: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$diagonal: bool;

axiom {:array_info "$$offDiagonal"} {:global} {:elem_width 32} {:source_name "offDiagonal"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$offDiagonal: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$offDiagonal: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$offDiagonal: bool;

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

function FDIV32(bv32, bv32) : bv32;

function FLT32(bv32, bv32) : bool;

function FMUL32(bv32, bv32) : bv32;

function FP32_TO_UI32(bv32) : bv32;

function FSUB32(bv32, bv32) : bv32;

function UI32_TO_FP32(bv32) : bv32;

function {:builtin "bvadd"} BV32_ADD(bv32, bv32) : bv32;

function {:builtin "bvmul"} BV32_MUL(bv32, bv32) : bv32;

function {:builtin "bvsub"} BV32_SUB(bv32, bv32) : bv32;

function {:builtin "bvult"} BV32_ULT(bv32, bv32) : bool;

procedure {:source_name "calNumEigenValueInterval"} {:kernel} ULTIMATE.start($width: bv32);
  requires !_READ_HAS_OCCURRED_$$numEigenIntervals && !_WRITE_HAS_OCCURRED_$$numEigenIntervals && !_ATOMIC_HAS_OCCURRED_$$numEigenIntervals;
  requires !_READ_HAS_OCCURRED_$$eigenIntervals && !_WRITE_HAS_OCCURRED_$$eigenIntervals && !_ATOMIC_HAS_OCCURRED_$$eigenIntervals;
  requires !_READ_HAS_OCCURRED_$$diagonal && !_WRITE_HAS_OCCURRED_$$diagonal && !_ATOMIC_HAS_OCCURRED_$$diagonal;
  requires !_READ_HAS_OCCURRED_$$offDiagonal && !_WRITE_HAS_OCCURRED_$$offDiagonal && !_ATOMIC_HAS_OCCURRED_$$offDiagonal;
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
  modifies _WRITE_HAS_OCCURRED_$$numEigenIntervals, _WRITE_READ_BENIGN_FLAG_$$numEigenIntervals, _WRITE_READ_BENIGN_FLAG_$$numEigenIntervals, $$numEigenIntervals ;



implementation {:source_name "calNumEigenValueInterval"} {:kernel} ULTIMATE.start($width: bv32)
{
  var $count.i.0$1: bv32;
  var $count.i.0$2: bv32;
  var $prev_diff.i.0$1: bv32;
  var $prev_diff.i.0$2: bv32;
  var $i.i.0: bv32;
  var $prev_diff.i13.0$1: bv32;
  var $prev_diff.i13.0$2: bv32;
  var $count.i12.0$1: bv32;
  var $count.i12.0$2: bv32;
  var $i.i14.0: bv32;
  var v2$1: bv32;
  var v2$2: bv32;
  var v0$1: bv32;
  var v0$2: bv32;
  var v1$1: bv32;
  var v1$2: bv32;
  var v3$1: bv32;
  var v3$2: bv32;
  var v4$1: bv32;
  var v4$2: bv32;
  var v5$1: bv32;
  var v5$2: bv32;
  var v6: bool;
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
  var v12$1: bv32;
  var v12$2: bv32;
  var v13: bool;
  var v14$1: bv32;
  var v14$2: bv32;
  var v15$1: bv32;
  var v15$2: bv32;
  var v16$1: bv32;
  var v16$2: bv32;
  var v17$1: bv32;
  var v17$2: bv32;
  
  var tmp,tmp2,tmp3: bv32;  

  $entry:
    v0$1 := BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1);
    v0$2 := BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2);
    v1$1 := BV32_MUL(2bv32, v0$1);
    v1$2 := BV32_MUL(2bv32, v0$2);
    havoc v2$1, v2$2;
    havoc v3$1, v3$2;
    havoc v4$1, v4$2;
    v5$1 := FSUB32(v4$1, v2$1);
    v5$2 := FSUB32(v4$2, v2$2);
    $count.i.0$1, $prev_diff.i.0$1, $i.i.0 := (if FLT32(v5$1, 0bv32) then 1bv32 else 0bv32), v5$1, 1bv32;
    $count.i.0$2, $prev_diff.i.0$2 := (if FLT32(v5$2, 0bv32) then 1bv32 else 0bv32), v5$2;
    assume {:captureState "loop_entry_state_1_0"} true;
    goto $for.cond.i;

  $for.cond.i:
    assume {:captureState "loop_head_state_1"} true;
    assert {:block_sourceloc} {:sourceloc_num 4} true;
    v6 := BV32_ULT($i.i.0, $width);
    goto $truebb, $falsebb;

  $falsebb:
    assume {:partition} !v6;
    havoc v11$1, v11$2;
    v12$1 := FSUB32(v11$1, v3$1);
    v12$2 := FSUB32(v11$2, v3$2);
    $prev_diff.i13.0$1, $count.i12.0$1, $i.i14.0 := v12$1, (if FLT32(v12$1, 0bv32) then 1bv32 else 0bv32), 1bv32;
    $prev_diff.i13.0$2, $count.i12.0$2 := v12$2, (if FLT32(v12$2, 0bv32) then 1bv32 else 0bv32);
    assume {:captureState "loop_entry_state_0_0"} true;
    goto $for.cond.i21;

  $for.cond.i21:
    assume {:captureState "loop_head_state_0"} true;
    assert {:block_sourceloc} {:sourceloc_num 11} true;
    v13 := BV32_ULT($i.i14.0, $width);
    goto $truebb0, $falsebb0;

  $falsebb0:
    assume {:partition} !v13;
    call  _LOG_WRITE_$$numEigenIntervals(true, v0$1, BV32_SUB(FP32_TO_UI32(UI32_TO_FP32($count.i12.0$1)), FP32_TO_UI32(UI32_TO_FP32($count.i.0$1))), $$numEigenIntervals[v0$1]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$numEigenIntervals(true, v0$2);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 17} true;
	tmp:=BV32_SUB(FP32_TO_UI32(UI32_TO_FP32($count.i12.0$2)), FP32_TO_UI32(UI32_TO_FP32($count.i.0$2)));
	tmp2:=_WATCHED_OFFSET;
	tmp3:=_WATCHED_VALUE_$$numEigenIntervals;
	//v0$2=0bv32, tmp=1bv32, tmp2=0bv32, tmp3=0bv32, _WRITE_HAS_OCCURRED_$$numEigenIntervals=true
    call  _CHECK_WRITE_$$numEigenIntervals(true, v0$2, tmp);
	//  _CHECK_WRITE_$$numEigenIntervals(_P: bool, _offset: bv32, _value: bv32);
	//	_P=true, _WRITE_HAS_OCCURRED_$$numEigenIntervals=true, _WATCHED_OFFSET=0bv32, _offset=0bv32, _WATCHED_VALUE_$$numEigenIntervals=0bvs32, _value=1bv32, 
	//  requires  !(_P && _WRITE_HAS_OCCURRED_$$numEigenIntervals && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$numEigenIntervals != _value);
    //  requires  !(_P && _READ_HAS_OCCURRED_$$numEigenIntervals && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$numEigenIntervals != _value);
    //  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$numEigenIntervals && _WATCHED_OFFSET == _offset);
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$numEigenIntervals"} true;
    $$numEigenIntervals[v0$1] := BV32_SUB(FP32_TO_UI32(UI32_TO_FP32($count.i12.0$1)), FP32_TO_UI32(UI32_TO_FP32($count.i.0$1)));
    $$numEigenIntervals[v0$2] := BV32_SUB(FP32_TO_UI32(UI32_TO_FP32($count.i12.0$2)), FP32_TO_UI32(UI32_TO_FP32($count.i.0$2)));
    return;

  $truebb0:
    assume {:partition} v13;
    havoc v14$1, v14$2;
    havoc v15$1, v15$2;
    havoc v16$1, v16$2;
    v17$1 := FSUB32(FSUB32(v14$1, v3$1), FDIV32(FMUL32(v15$1, v16$1), $prev_diff.i13.0$1));
    v17$2 := FSUB32(FSUB32(v14$2, v3$2), FDIV32(FMUL32(v15$2, v16$2), $prev_diff.i13.0$2));
    $prev_diff.i13.0$1, $count.i12.0$1, $i.i14.0 := v17$1, BV32_ADD($count.i12.0$1, (if FLT32(v17$1, 0bv32) then 1bv32 else 0bv32)), BV32_ADD($i.i14.0, 1bv32);
    $prev_diff.i13.0$2, $count.i12.0$2 := v17$2, BV32_ADD($count.i12.0$2, (if FLT32(v17$2, 0bv32) then 1bv32 else 0bv32));
    assume {:captureState "loop_back_edge_state_0_0"} true;
    goto $for.cond.i21;

  $truebb:
    assume {:partition} v6;
    havoc v7$1, v7$2;
    havoc v8$1, v8$2;
    havoc v9$1, v9$2;
    v10$1 := FSUB32(FSUB32(v7$1, v2$1), FDIV32(FMUL32(v8$1, v9$1), $prev_diff.i.0$1));
    v10$2 := FSUB32(FSUB32(v7$2, v2$2), FDIV32(FMUL32(v8$2, v9$2), $prev_diff.i.0$2));
    $count.i.0$1, $prev_diff.i.0$1, $i.i.0 := BV32_ADD($count.i.0$1, (if FLT32(v10$1, 0bv32) then 1bv32 else 0bv32)), v10$1, BV32_ADD($i.i.0, 1bv32);
    $count.i.0$2, $prev_diff.i.0$2 := BV32_ADD($count.i.0$2, (if FLT32(v10$2, 0bv32) then 1bv32 else 0bv32)), v10$2;
    assume {:captureState "loop_back_edge_state_1_0"} true;
    goto $for.cond.i;
}



axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 256bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 4bv32 then 1bv1 else 0bv1) != 0bv1;

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

const _WATCHED_VALUE_$$numEigenIntervals: bv32;

procedure {:inline 1} _LOG_READ_$$numEigenIntervals(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$numEigenIntervals;



implementation {:inline 1} _LOG_READ_$$numEigenIntervals(_P: bool, _offset: bv32, _value: bv32)
{
  log_access_entry:
    _READ_HAS_OCCURRED_$$numEigenIntervals := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$numEigenIntervals == _value then true else _READ_HAS_OCCURRED_$$numEigenIntervals);
    return;
}



procedure _CHECK_READ_$$numEigenIntervals(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$numEigenIntervals && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$numEigenIntervals);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$numEigenIntervals && _WATCHED_OFFSET == _offset);



var _WRITE_READ_BENIGN_FLAG_$$numEigenIntervals: bool;

procedure {:inline 1} _LOG_WRITE_$$numEigenIntervals(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$numEigenIntervals, _WRITE_READ_BENIGN_FLAG_$$numEigenIntervals;



implementation {:inline 1} _LOG_WRITE_$$numEigenIntervals(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$numEigenIntervals := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$numEigenIntervals == _value then true else _WRITE_HAS_OCCURRED_$$numEigenIntervals);
    _WRITE_READ_BENIGN_FLAG_$$numEigenIntervals := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$numEigenIntervals == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$numEigenIntervals);
    return;
}



procedure _CHECK_WRITE_$$numEigenIntervals(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$numEigenIntervals && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$numEigenIntervals != _value);
  requires  !(_P && _READ_HAS_OCCURRED_$$numEigenIntervals && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$numEigenIntervals != _value);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$numEigenIntervals && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _LOG_ATOMIC_$$numEigenIntervals(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$numEigenIntervals;



implementation {:inline 1} _LOG_ATOMIC_$$numEigenIntervals(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$numEigenIntervals := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$numEigenIntervals);
    return;
}



procedure _CHECK_ATOMIC_$$numEigenIntervals(_P: bool, _offset: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$numEigenIntervals && _WATCHED_OFFSET == _offset);
  requires  !(_P && _READ_HAS_OCCURRED_$$numEigenIntervals && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$numEigenIntervals(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$numEigenIntervals;



implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$numEigenIntervals(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$numEigenIntervals := (if _P && _WRITE_HAS_OCCURRED_$$numEigenIntervals && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$numEigenIntervals);
    return;
}



const _WATCHED_VALUE_$$eigenIntervals: bv32;

procedure {:inline 1} _LOG_READ_$$eigenIntervals(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$eigenIntervals;



implementation {:inline 1} _LOG_READ_$$eigenIntervals(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$eigenIntervals := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$eigenIntervals == _value then true else _READ_HAS_OCCURRED_$$eigenIntervals);
    return;
}



procedure _CHECK_READ_$$eigenIntervals(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$eigenIntervals && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$eigenIntervals);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$eigenIntervals && _WATCHED_OFFSET == _offset);



var _WRITE_READ_BENIGN_FLAG_$$eigenIntervals: bool;

procedure {:inline 1} _LOG_WRITE_$$eigenIntervals(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$eigenIntervals, _WRITE_READ_BENIGN_FLAG_$$eigenIntervals;



implementation {:inline 1} _LOG_WRITE_$$eigenIntervals(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$eigenIntervals := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$eigenIntervals == _value then true else _WRITE_HAS_OCCURRED_$$eigenIntervals);
    _WRITE_READ_BENIGN_FLAG_$$eigenIntervals := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$eigenIntervals == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$eigenIntervals);
    return;
}



procedure _CHECK_WRITE_$$eigenIntervals(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$eigenIntervals && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$eigenIntervals != _value);
  requires  !(_P && _READ_HAS_OCCURRED_$$eigenIntervals && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$eigenIntervals != _value);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$eigenIntervals && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _LOG_ATOMIC_$$eigenIntervals(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$eigenIntervals;



implementation {:inline 1} _LOG_ATOMIC_$$eigenIntervals(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$eigenIntervals := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$eigenIntervals);
    return;
}



procedure _CHECK_ATOMIC_$$eigenIntervals(_P: bool, _offset: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$eigenIntervals && _WATCHED_OFFSET == _offset);
  requires  !(_P && _READ_HAS_OCCURRED_$$eigenIntervals && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$eigenIntervals(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$eigenIntervals;



implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$eigenIntervals(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$eigenIntervals := (if _P && _WRITE_HAS_OCCURRED_$$eigenIntervals && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$eigenIntervals);
    return;
}



const _WATCHED_VALUE_$$diagonal: bv32;

procedure {:inline 1} _LOG_READ_$$diagonal(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$diagonal;



implementation {:inline 1} _LOG_READ_$$diagonal(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$diagonal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$diagonal == _value then true else _READ_HAS_OCCURRED_$$diagonal);
    return;
}



procedure _CHECK_READ_$$diagonal(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$diagonal && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$diagonal);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$diagonal && _WATCHED_OFFSET == _offset);



var _WRITE_READ_BENIGN_FLAG_$$diagonal: bool;

procedure {:inline 1} _LOG_WRITE_$$diagonal(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$diagonal, _WRITE_READ_BENIGN_FLAG_$$diagonal;



implementation {:inline 1} _LOG_WRITE_$$diagonal(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$diagonal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$diagonal == _value then true else _WRITE_HAS_OCCURRED_$$diagonal);
    _WRITE_READ_BENIGN_FLAG_$$diagonal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$diagonal == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$diagonal);
    return;
}



procedure _CHECK_WRITE_$$diagonal(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$diagonal && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$diagonal != _value);
  requires  !(_P && _READ_HAS_OCCURRED_$$diagonal && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$diagonal != _value);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$diagonal && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _LOG_ATOMIC_$$diagonal(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$diagonal;



implementation {:inline 1} _LOG_ATOMIC_$$diagonal(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$diagonal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$diagonal);
    return;
}



procedure _CHECK_ATOMIC_$$diagonal(_P: bool, _offset: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$diagonal && _WATCHED_OFFSET == _offset);
  requires  !(_P && _READ_HAS_OCCURRED_$$diagonal && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$diagonal(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$diagonal;



implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$diagonal(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$diagonal := (if _P && _WRITE_HAS_OCCURRED_$$diagonal && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$diagonal);
    return;
}



const _WATCHED_VALUE_$$offDiagonal: bv32;

procedure {:inline 1} _LOG_READ_$$offDiagonal(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$offDiagonal;



implementation {:inline 1} _LOG_READ_$$offDiagonal(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$offDiagonal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$offDiagonal == _value then true else _READ_HAS_OCCURRED_$$offDiagonal);
    return;
}



procedure _CHECK_READ_$$offDiagonal(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$offDiagonal && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$offDiagonal);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$offDiagonal && _WATCHED_OFFSET == _offset);



var _WRITE_READ_BENIGN_FLAG_$$offDiagonal: bool;

procedure {:inline 1} _LOG_WRITE_$$offDiagonal(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$offDiagonal, _WRITE_READ_BENIGN_FLAG_$$offDiagonal;



implementation {:inline 1} _LOG_WRITE_$$offDiagonal(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$offDiagonal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$offDiagonal == _value then true else _WRITE_HAS_OCCURRED_$$offDiagonal);
    _WRITE_READ_BENIGN_FLAG_$$offDiagonal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$offDiagonal == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$offDiagonal);
    return;
}



procedure _CHECK_WRITE_$$offDiagonal(_P: bool, _offset: bv32, _value: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$offDiagonal && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$offDiagonal != _value);
  requires  !(_P && _READ_HAS_OCCURRED_$$offDiagonal && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$offDiagonal != _value);
  requires  !(_P && _ATOMIC_HAS_OCCURRED_$$offDiagonal && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _LOG_ATOMIC_$$offDiagonal(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$offDiagonal;



implementation {:inline 1} _LOG_ATOMIC_$$offDiagonal(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$offDiagonal := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$offDiagonal);
    return;
}



procedure _CHECK_ATOMIC_$$offDiagonal(_P: bool, _offset: bv32);
  requires  !(_P && _WRITE_HAS_OCCURRED_$$offDiagonal && _WATCHED_OFFSET == _offset);
  requires  !(_P && _READ_HAS_OCCURRED_$$offDiagonal && _WATCHED_OFFSET == _offset);



procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$offDiagonal(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$offDiagonal;



implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$offDiagonal(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$offDiagonal := (if _P && _WRITE_HAS_OCCURRED_$$offDiagonal && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$offDiagonal);
    return;
}



var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
