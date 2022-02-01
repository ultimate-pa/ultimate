//#Safe
type _SIZE_T_TYPE = bv32;

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

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;

function {:builtin "bvsub"} BV32_SUB(bv32, bv32) : bv32;

procedure {:source_name "binomial_options_kernel"} ULTIMATE.start();
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
  modifies _TRACKING, _TRACKING, _TRACKING;

implementation {:source_name "binomial_options_kernel"} ULTIMATE.start()
{
  var $i.0: bv32;
  var $c_base.0: bv32;
  var $k.0: bv32;
  var v0: bool;
  var v1: bool;
  var v2: bool;

  $entry:
    $i.0 := 1024bv32;
    assume {:captureState "loop_entry_state_0_0"} true;
    goto $for.cond;

  $for.cond:
    assume {:captureState "loop_head_state_0"} true;
    assert {:block_sourceloc} {:sourceloc_num 1} true;
    v0 := BV32_SGT($i.0, 0bv32);
    goto $truebb, $falsebb;

  $falsebb:
    assume {:partition} !v0;
    return;

  $truebb:
    assume {:partition} v0;
    $c_base.0 := 0bv32;
    assume {:captureState "loop_entry_state_1_0"} true;
    goto $for.cond1;

  $for.cond1:
    assume {:captureState "loop_head_state_1"} true;
    assert {:block_sourceloc} {:sourceloc_num 3} true;
    v1 := BV32_SLT($c_base.0, $i.0);
    goto __partitioned_block_$truebb0_0, $falsebb0;

  $falsebb0:
    assume {:partition} !v1;
    $i.0 := BV32_SUB($i.0, 16bv32);
    assume {:captureState "loop_back_edge_state_0_0"} true;
    goto $for.cond;

  __partitioned_block_$truebb0_0:
    assume {:partition} v1;
    goto __partitioned_block_$truebb0_1;

  __partitioned_block_$truebb0_1:
    call $bugle_barrier_duplicated_0(1bv1, 0bv1);
    $k.0 := 254bv32;
    assume {:captureState "loop_entry_state_2_0"} true;
    goto $for.cond5;

  $for.cond5:
    assume {:captureState "loop_head_state_2"} true;
    assert {:block_sourceloc} {:sourceloc_num 6} true;
    v2 := BV32_SGE($k.0, 239bv32);
    goto __partitioned_block_$truebb1_0, __partitioned_block_$falsebb1_0;

  __partitioned_block_$falsebb1_0:
    assume {:partition} !v2;
    goto __partitioned_block_$falsebb1_1;

  __partitioned_block_$falsebb1_1:
    call $bugle_barrier_duplicated_1(1bv1, 0bv1);
    $c_base.0 := BV32_ADD($c_base.0, 240bv32);
    assume {:captureState "loop_back_edge_state_1_0"} true;
    goto $for.cond1;

  __partitioned_block_$truebb1_0:
    assume {:partition} v2;
    goto __partitioned_block_$truebb1_1;

  __partitioned_block_$truebb1_1:
    call $bugle_barrier_duplicated_2(1bv1, 0bv1);
    $k.0 := BV32_ADD($k.0, 4294967295bv32);
    assume {:captureState "loop_back_edge_state_2_0"} true;
    goto $for.cond5;
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

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_0($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 0bv1;
  modifies _TRACKING;

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_1($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 0bv1;
  modifies _TRACKING;

procedure {:inline 1} {:safe_barrier} {:source_name "bugle_barrier"} {:barrier} $bugle_barrier_duplicated_2($0: bv1, $1: bv1);
  requires $0 == 1bv1;
  requires $1 == 0bv1;
  modifies _TRACKING;

var _TRACKING: bool;

implementation {:inline 1} $bugle_barrier_duplicated_0($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon1_Then, anon1_Else;

  anon1_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    havoc _TRACKING;
    return;

  anon1_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

implementation {:inline 1} $bugle_barrier_duplicated_1($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon1_Then, anon1_Else;

  anon1_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    havoc _TRACKING;
    return;

  anon1_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

implementation {:inline 1} $bugle_barrier_duplicated_2($0: bv1, $1: bv1)
{

  __BarrierImpl:
    goto anon1_Then, anon1_Else;

  anon1_Else:
    assume {:partition} true;
    goto anon0;

  anon0:
    havoc _TRACKING;
    return;

  anon1_Then:
    assume {:partition} false;
    goto __Disabled;

  __Disabled:
    return;
}

