//#Unsafe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

axiom {:array_info "$$p1"} {:global} {:elem_width 32} {:source_name "p1"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$p1: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$p1: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$p1: bool;

const $arrayId$$p1: arrayId;

axiom $arrayId$$p1 == 1bv3;

axiom {:array_info "$$p2"} {:global} {:elem_width 32} {:source_name "p2"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$p2: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$p2: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$p2: bool;

const $arrayId$$p2: arrayId;

axiom $arrayId$$p2 == 2bv3;

axiom {:array_info "$$p3"} {:global} {:elem_width 32} {:source_name "p3"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$p3: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$p3: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$p3: bool;

const $arrayId$$p3: arrayId;

axiom $arrayId$$p3 == 3bv3;

axiom {:array_info "$$p4"} {:global} {:elem_width 32} {:source_name "p4"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$p4: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$p4: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$p4: bool;

const $arrayId$$p4: arrayId;

axiom $arrayId$$p4 == 4bv3;

axiom {:array_info "$$p5"} {:global} {:elem_width 32} {:source_name "p5"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$p5: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$p5: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$p5: bool;

const $arrayId$$p5: arrayId;

axiom $arrayId$$p5 == 5bv3;

axiom {:array_info "$$p6"} {:global} {:elem_width 32} {:source_name "p6"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$p6: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$p6: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$p6: bool;

const $arrayId$$p6: arrayId;

axiom $arrayId$$p6 == 6bv3;

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

type functionPtr = bv3;

const $functionId$$_Z1aPf: functionPtr;

axiom $functionId$$_Z1aPf == 1bv3;

const $functionId$$_Z1bPf: functionPtr;

axiom $functionId$$_Z1bPf == 2bv3;

const $functionId$$_Z1cPf: functionPtr;

axiom $functionId$$_Z1cPf == 3bv3;

const $functionId$$_Z1dPf: functionPtr;

axiom $functionId$$_Z1dPf == 4bv3;

const $functionId$$_Z1ePf: functionPtr;

axiom $functionId$$_Z1ePf == 5bv3;

const $functionId$$_Z11should_failPfS_S_S_S_S_ii: functionPtr;

axiom $functionId$$_Z11should_failPfS_S_S_S_S_ii == 6bv3;

const $functionId$$null$: functionPtr;

axiom $functionId$$null$ == 0bv3;

const {:group_size_x} group_size_x: bv32;

const {:group_size_y} group_size_y: bv32;

const {:group_size_z} group_size_z: bv32;

const {:num_groups_x} num_groups_x: bv32;

const {:num_groups_y} num_groups_y: bv32;

const {:num_groups_z} num_groups_z: bv32;

procedure {:source_name "a"} $_Z1aPf($v: ptr);
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

implementation {:source_name "a"} $_Z1aPf($v: ptr)
{

  $entry:
    return;
}

procedure {:source_name "b"} $_Z1bPf($v: ptr);
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

implementation {:source_name "b"} $_Z1bPf($v: ptr)
{

  $entry:
    return;
}

procedure {:source_name "c"} $_Z1cPf($v: ptr);
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

implementation {:source_name "c"} $_Z1cPf($v: ptr)
{

  $entry:
    return;
}

procedure {:source_name "d"} $_Z1dPf($v: ptr);
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

implementation {:source_name "d"} $_Z1dPf($v: ptr)
{

  $entry:
    return;
}

procedure {:source_name "e"} $_Z1ePf($v: ptr);
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

implementation {:source_name "e"} $_Z1ePf($v: ptr)
{

  $entry:
    return;
}

procedure {:source_name "should_fail"} ULTIMATE.start($x: bv32, $y: bv32);
  requires !_READ_HAS_OCCURRED_$$p1 && !_WRITE_HAS_OCCURRED_$$p1 && !_ATOMIC_HAS_OCCURRED_$$p1;
  requires !_READ_HAS_OCCURRED_$$p2 && !_WRITE_HAS_OCCURRED_$$p2 && !_ATOMIC_HAS_OCCURRED_$$p2;
  requires !_READ_HAS_OCCURRED_$$p3 && !_WRITE_HAS_OCCURRED_$$p3 && !_ATOMIC_HAS_OCCURRED_$$p3;
  requires !_READ_HAS_OCCURRED_$$p4 && !_WRITE_HAS_OCCURRED_$$p4 && !_ATOMIC_HAS_OCCURRED_$$p4;
  requires !_READ_HAS_OCCURRED_$$p5 && !_WRITE_HAS_OCCURRED_$$p5 && !_ATOMIC_HAS_OCCURRED_$$p5;
  requires !_READ_HAS_OCCURRED_$$p6 && !_WRITE_HAS_OCCURRED_$$p6 && !_ATOMIC_HAS_OCCURRED_$$p6;
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

implementation {:source_name "should_fail"} ULTIMATE.start($x: bv32, $y: bv32)
{
  var $fp.0: functionPtr;

  $entry:
    goto $casebb, $casebb0, $casebb1, $casebb2, $defaultbb;

  $defaultbb:
    assume {:partition} $x != 1bv32 && $x != 2bv32 && $x != 3bv32 && $x != 4bv32;
    $fp.0 := $functionId$$_Z1ePf;
    goto $sw.epilog;

  $sw.epilog:
    goto $casebb3, $casebb4, $casebb5, $casebb6, $defaultbb0;

  $defaultbb0:
    assume {:partition} $x != 1bv32 && $x != 2bv32 && $x != 3bv32 && $x != 4bv32;
    goto anon55_Then, anon55_Else;

  anon55_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1dPf;
    goto anon56_Then, anon56_Else;

  anon56_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1aPf;
    goto anon57_Then, anon57_Else;

  anon57_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1bPf;
    goto anon58_Then, anon58_Else;

  anon58_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1cPf;
    goto anon59_Then, anon59_Else;

  anon59_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1ePf;
    assert {:bad_pointer_access} {:sourceloc_num 46} {:thread 1} false;
    goto anon34;

  anon34:
    goto $sw.epilog9;

  $sw.epilog9:
    assert {:sourceloc_num 48} {:thread 1} false;
    return;

  anon59_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1ePf;
    call $_Z1ePf(MKPTR($arrayId$$p5, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1ePf"} true;
    goto anon34;

  anon58_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1cPf;
    call $_Z1cPf(MKPTR($arrayId$$p5, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1cPf"} true;
    goto anon34;

  anon57_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1bPf;
    call $_Z1bPf(MKPTR($arrayId$$p5, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1bPf"} true;
    goto anon34;

  anon56_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1aPf;
    call $_Z1aPf(MKPTR($arrayId$$p5, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1aPf"} true;
    goto anon34;

  anon55_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1dPf;
    call $_Z1dPf(MKPTR($arrayId$$p5, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1dPf"} true;
    goto anon34;

  $casebb6:
    assume {:partition} $x == 4bv32;
    goto anon50_Then, anon50_Else;

  anon50_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1dPf;
    goto anon51_Then, anon51_Else;

  anon51_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1aPf;
    goto anon52_Then, anon52_Else;

  anon52_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1bPf;
    goto anon53_Then, anon53_Else;

  anon53_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1cPf;
    goto anon54_Then, anon54_Else;

  anon54_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1ePf;
    assert {:bad_pointer_access} {:sourceloc_num 39} {:thread 1} false;
    goto anon27;

  anon27:
    goto $sw.epilog9;

  anon54_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1ePf;
    call $_Z1ePf(MKPTR($arrayId$$p4, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1ePf"} true;
    goto anon27;

  anon53_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1cPf;
    call $_Z1cPf(MKPTR($arrayId$$p4, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1cPf"} true;
    goto anon27;

  anon52_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1bPf;
    call $_Z1bPf(MKPTR($arrayId$$p4, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1bPf"} true;
    goto anon27;

  anon51_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1aPf;
    call $_Z1aPf(MKPTR($arrayId$$p4, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1aPf"} true;
    goto anon27;

  anon50_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1dPf;
    call $_Z1dPf(MKPTR($arrayId$$p4, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1dPf"} true;
    goto anon27;

  $casebb5:
    assume {:partition} $x == 3bv32;
    goto anon45_Then, anon45_Else;

  anon45_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1dPf;
    goto anon46_Then, anon46_Else;

  anon46_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1aPf;
    goto anon47_Then, anon47_Else;

  anon47_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1bPf;
    goto anon48_Then, anon48_Else;

  anon48_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1cPf;
    goto anon49_Then, anon49_Else;

  anon49_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1ePf;
    assert {:bad_pointer_access} {:sourceloc_num 32} {:thread 1} false;
    goto anon20;

  anon20:
    goto $sw.epilog9;

  anon49_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1ePf;
    call $_Z1ePf(MKPTR($arrayId$$p3, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1ePf"} true;
    goto anon20;

  anon48_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1cPf;
    call $_Z1cPf(MKPTR($arrayId$$p3, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1cPf"} true;
    goto anon20;

  anon47_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1bPf;
    call $_Z1bPf(MKPTR($arrayId$$p3, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1bPf"} true;
    goto anon20;

  anon46_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1aPf;
    call $_Z1aPf(MKPTR($arrayId$$p3, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1aPf"} true;
    goto anon20;

  anon45_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1dPf;
    call $_Z1dPf(MKPTR($arrayId$$p3, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1dPf"} true;
    goto anon20;

  $casebb4:
    assume {:partition} $x == 2bv32;
    goto anon40_Then, anon40_Else;

  anon40_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1dPf;
    goto anon41_Then, anon41_Else;

  anon41_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1aPf;
    goto anon42_Then, anon42_Else;

  anon42_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1bPf;
    goto anon43_Then, anon43_Else;

  anon43_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1cPf;
    goto anon44_Then, anon44_Else;

  anon44_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1ePf;
    assert {:bad_pointer_access} {:sourceloc_num 25} {:thread 1} false;
    goto anon13;

  anon13:
    goto $sw.epilog9;

  anon44_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1ePf;
    call $_Z1ePf(MKPTR($arrayId$$p2, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1ePf"} true;
    goto anon13;

  anon43_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1cPf;
    call $_Z1cPf(MKPTR($arrayId$$p2, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1cPf"} true;
    goto anon13;

  anon42_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1bPf;
    call $_Z1bPf(MKPTR($arrayId$$p2, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1bPf"} true;
    goto anon13;

  anon41_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1aPf;
    call $_Z1aPf(MKPTR($arrayId$$p2, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1aPf"} true;
    goto anon13;

  anon40_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1dPf;
    call $_Z1dPf(MKPTR($arrayId$$p2, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1dPf"} true;
    goto anon13;

  $casebb3:
    assume {:partition} $x == 1bv32;
    goto anon35_Then, anon35_Else;

  anon35_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1dPf;
    goto anon36_Then, anon36_Else;

  anon36_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1aPf;
    goto anon37_Then, anon37_Else;

  anon37_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1bPf;
    goto anon38_Then, anon38_Else;

  anon38_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1cPf;
    goto anon39_Then, anon39_Else;

  anon39_Else:
    assume {:partition} $fp.0 != $functionId$$_Z1ePf;
    assert {:bad_pointer_access} {:sourceloc_num 18} {:thread 1} false;
    goto anon6;

  anon6:
    goto $sw.epilog9;

  anon39_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1ePf;
    call $_Z1ePf(MKPTR($arrayId$$p1, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1ePf"} true;
    goto anon6;

  anon38_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1cPf;
    call $_Z1cPf(MKPTR($arrayId$$p1, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1cPf"} true;
    goto anon6;

  anon37_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1bPf;
    call $_Z1bPf(MKPTR($arrayId$$p1, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1bPf"} true;
    goto anon6;

  anon36_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1aPf;
    call $_Z1aPf(MKPTR($arrayId$$p1, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1aPf"} true;
    goto anon6;

  anon35_Then:
    assume {:partition} $fp.0 == $functionId$$_Z1dPf;
    call $_Z1dPf(MKPTR($arrayId$$p1, 0bv32));
    assume {:captureState "call_return_state_0"} {:procedureName "$_Z1dPf"} true;
    goto anon6;

  $casebb2:
    assume {:partition} $x == 4bv32;
    $fp.0 := $functionId$$_Z1dPf;
    goto $sw.epilog;

  $casebb1:
    assume {:partition} $x == 3bv32;
    $fp.0 := $functionId$$_Z1cPf;
    goto $sw.epilog;

  $casebb0:
    assume {:partition} $x == 2bv32;
    $fp.0 := $functionId$$_Z1bPf;
    goto $sw.epilog;

  $casebb:
    assume {:partition} $x == 1bv32;
    $fp.0 := $functionId$$_Z1aPf;
    goto $sw.epilog;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 128bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 16bv32 then 1bv1 else 0bv1) != 0bv1;

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

const _WATCHED_VALUE_$$p1: bv32;

procedure {:inline 1} _LOG_READ_$$p1(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$p1;

implementation {:inline 1} _LOG_READ_$$p1(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$p1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p1 == _value then true else _READ_HAS_OCCURRED_$$p1);
    return;
}

procedure _CHECK_READ_$$p1(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p1 && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$p1);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p1 && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$p1: bool;

procedure {:inline 1} _LOG_WRITE_$$p1(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$p1, _WRITE_READ_BENIGN_FLAG_$$p1;

implementation {:inline 1} _LOG_WRITE_$$p1(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$p1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p1 == _value then true else _WRITE_HAS_OCCURRED_$$p1);
    _WRITE_READ_BENIGN_FLAG_$$p1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p1 == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$p1);
    return;
}

procedure _CHECK_WRITE_$$p1(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p1 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p1 != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$p1 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p1 != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p1 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$p1(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$p1;

implementation {:inline 1} _LOG_ATOMIC_$$p1(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$p1 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$p1);
    return;
}

procedure _CHECK_ATOMIC_$$p1(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p1 && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$p1 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p1(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$p1;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p1(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$p1 := (if _P && _WRITE_HAS_OCCURRED_$$p1 && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$p1);
    return;
}

const _WATCHED_VALUE_$$p2: bv32;

procedure {:inline 1} _LOG_READ_$$p2(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$p2;

implementation {:inline 1} _LOG_READ_$$p2(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$p2 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p2 == _value then true else _READ_HAS_OCCURRED_$$p2);
    return;
}

procedure _CHECK_READ_$$p2(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p2 && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$p2);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p2 && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$p2: bool;

procedure {:inline 1} _LOG_WRITE_$$p2(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$p2, _WRITE_READ_BENIGN_FLAG_$$p2;

implementation {:inline 1} _LOG_WRITE_$$p2(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$p2 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p2 == _value then true else _WRITE_HAS_OCCURRED_$$p2);
    _WRITE_READ_BENIGN_FLAG_$$p2 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p2 == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$p2);
    return;
}

procedure _CHECK_WRITE_$$p2(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p2 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p2 != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$p2 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p2 != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p2 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$p2(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$p2;

implementation {:inline 1} _LOG_ATOMIC_$$p2(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$p2 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$p2);
    return;
}

procedure _CHECK_ATOMIC_$$p2(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p2 && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$p2 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p2(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$p2;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p2(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$p2 := (if _P && _WRITE_HAS_OCCURRED_$$p2 && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$p2);
    return;
}

const _WATCHED_VALUE_$$p3: bv32;

procedure {:inline 1} _LOG_READ_$$p3(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$p3;

implementation {:inline 1} _LOG_READ_$$p3(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$p3 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p3 == _value then true else _READ_HAS_OCCURRED_$$p3);
    return;
}

procedure _CHECK_READ_$$p3(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p3 && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$p3);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p3 && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$p3: bool;

procedure {:inline 1} _LOG_WRITE_$$p3(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$p3, _WRITE_READ_BENIGN_FLAG_$$p3;

implementation {:inline 1} _LOG_WRITE_$$p3(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$p3 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p3 == _value then true else _WRITE_HAS_OCCURRED_$$p3);
    _WRITE_READ_BENIGN_FLAG_$$p3 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p3 == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$p3);
    return;
}

procedure _CHECK_WRITE_$$p3(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p3 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p3 != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$p3 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p3 != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p3 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$p3(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$p3;

implementation {:inline 1} _LOG_ATOMIC_$$p3(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$p3 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$p3);
    return;
}

procedure _CHECK_ATOMIC_$$p3(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p3 && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$p3 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p3(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$p3;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p3(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$p3 := (if _P && _WRITE_HAS_OCCURRED_$$p3 && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$p3);
    return;
}

const _WATCHED_VALUE_$$p4: bv32;

procedure {:inline 1} _LOG_READ_$$p4(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$p4;

implementation {:inline 1} _LOG_READ_$$p4(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$p4 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p4 == _value then true else _READ_HAS_OCCURRED_$$p4);
    return;
}

procedure _CHECK_READ_$$p4(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p4 && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$p4);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p4 && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$p4: bool;

procedure {:inline 1} _LOG_WRITE_$$p4(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$p4, _WRITE_READ_BENIGN_FLAG_$$p4;

implementation {:inline 1} _LOG_WRITE_$$p4(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$p4 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p4 == _value then true else _WRITE_HAS_OCCURRED_$$p4);
    _WRITE_READ_BENIGN_FLAG_$$p4 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p4 == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$p4);
    return;
}

procedure _CHECK_WRITE_$$p4(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p4 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p4 != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$p4 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p4 != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p4 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$p4(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$p4;

implementation {:inline 1} _LOG_ATOMIC_$$p4(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$p4 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$p4);
    return;
}

procedure _CHECK_ATOMIC_$$p4(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p4 && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$p4 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p4(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$p4;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p4(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$p4 := (if _P && _WRITE_HAS_OCCURRED_$$p4 && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$p4);
    return;
}

const _WATCHED_VALUE_$$p5: bv32;

procedure {:inline 1} _LOG_READ_$$p5(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$p5;

implementation {:inline 1} _LOG_READ_$$p5(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$p5 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p5 == _value then true else _READ_HAS_OCCURRED_$$p5);
    return;
}

procedure _CHECK_READ_$$p5(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p5 && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$p5);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p5 && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$p5: bool;

procedure {:inline 1} _LOG_WRITE_$$p5(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$p5, _WRITE_READ_BENIGN_FLAG_$$p5;

implementation {:inline 1} _LOG_WRITE_$$p5(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$p5 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p5 == _value then true else _WRITE_HAS_OCCURRED_$$p5);
    _WRITE_READ_BENIGN_FLAG_$$p5 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p5 == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$p5);
    return;
}

procedure _CHECK_WRITE_$$p5(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p5 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p5 != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$p5 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p5 != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p5 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$p5(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$p5;

implementation {:inline 1} _LOG_ATOMIC_$$p5(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$p5 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$p5);
    return;
}

procedure _CHECK_ATOMIC_$$p5(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p5 && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$p5 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p5(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$p5;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p5(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$p5 := (if _P && _WRITE_HAS_OCCURRED_$$p5 && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$p5);
    return;
}

const _WATCHED_VALUE_$$p6: bv32;

procedure {:inline 1} _LOG_READ_$$p6(_P: bool, _offset: bv32, _value: bv32);
  modifies _READ_HAS_OCCURRED_$$p6;

implementation {:inline 1} _LOG_READ_$$p6(_P: bool, _offset: bv32, _value: bv32)
{

  log_access_entry:
    _READ_HAS_OCCURRED_$$p6 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p6 == _value then true else _READ_HAS_OCCURRED_$$p6);
    return;
}

procedure _CHECK_READ_$$p6(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p6 && _WATCHED_OFFSET == _offset && _WRITE_READ_BENIGN_FLAG_$$p6);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p6 && _WATCHED_OFFSET == _offset);

var _WRITE_READ_BENIGN_FLAG_$$p6: bool;

procedure {:inline 1} _LOG_WRITE_$$p6(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32);
  modifies _WRITE_HAS_OCCURRED_$$p6, _WRITE_READ_BENIGN_FLAG_$$p6;

implementation {:inline 1} _LOG_WRITE_$$p6(_P: bool, _offset: bv32, _value: bv32, _value_old: bv32)
{

  log_access_entry:
    _WRITE_HAS_OCCURRED_$$p6 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p6 == _value then true else _WRITE_HAS_OCCURRED_$$p6);
    _WRITE_READ_BENIGN_FLAG_$$p6 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p6 == _value then _value != _value_old else _WRITE_READ_BENIGN_FLAG_$$p6);
    return;
}

procedure _CHECK_WRITE_$$p6(_P: bool, _offset: bv32, _value: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p6 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p6 != _value);
  requires !(_P && _READ_HAS_OCCURRED_$$p6 && _WATCHED_OFFSET == _offset && _WATCHED_VALUE_$$p6 != _value);
  requires !(_P && _ATOMIC_HAS_OCCURRED_$$p6 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _LOG_ATOMIC_$$p6(_P: bool, _offset: bv32);
  modifies _ATOMIC_HAS_OCCURRED_$$p6;

implementation {:inline 1} _LOG_ATOMIC_$$p6(_P: bool, _offset: bv32)
{

  log_access_entry:
    _ATOMIC_HAS_OCCURRED_$$p6 := (if _P && _TRACKING && _WATCHED_OFFSET == _offset then true else _ATOMIC_HAS_OCCURRED_$$p6);
    return;
}

procedure _CHECK_ATOMIC_$$p6(_P: bool, _offset: bv32);
  requires !(_P && _WRITE_HAS_OCCURRED_$$p6 && _WATCHED_OFFSET == _offset);
  requires !(_P && _READ_HAS_OCCURRED_$$p6 && _WATCHED_OFFSET == _offset);

procedure {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p6(_P: bool, _offset: bv32);
  modifies _WRITE_READ_BENIGN_FLAG_$$p6;

implementation {:inline 1} _UPDATE_WRITE_READ_BENIGN_FLAG_$$p6(_P: bool, _offset: bv32)
{

  _UPDATE_BENIGN_FLAG:
    _WRITE_READ_BENIGN_FLAG_$$p6 := (if _P && _WRITE_HAS_OCCURRED_$$p6 && _WATCHED_OFFSET == _offset then false else _WRITE_READ_BENIGN_FLAG_$$p6);
    return;
}

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
