//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

axiom {:array_info "$$x.addr"} {:elem_width 32} {:source_name "x.addr"} {:source_elem_width 128} {:source_dimensions "1"} true;

axiom {:array_info "$$y.addr"} {:elem_width 32} {:source_name "y.addr"} {:source_elem_width 128} {:source_dimensions "1"} true;

axiom {:array_info "$$temp"} {:elem_width 32} {:source_name "temp"} {:source_elem_width 128} {:source_dimensions "1"} true;

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

function FMIN32(bv32, bv32) : bv32;

procedure {:source_name "foo"} ULTIMATE.start($x: bv96, $y: bv96);
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

implementation {:source_name "foo"} ULTIMATE.start($x: bv96, $y: bv96)
{
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
  var v6$1: bv32;
  var v6$2: bv32;
  var v7$1: bv32;
  var v7$2: bv32;

  $entry:
    $$x.addr$0bv32$1 := $x[32:0];
    $$x.addr$0bv32$2 := $x[32:0];
    $$x.addr$1bv32$1 := $x[64:32];
    $$x.addr$1bv32$2 := $x[64:32];
    $$x.addr$2bv32$1 := $x[96:64];
    $$x.addr$2bv32$2 := $x[96:64];
    $$x.addr$3bv32$1 := 0bv32;
    $$x.addr$3bv32$2 := 0bv32;
    $$y.addr$0bv32$1 := $y[32:0];
    $$y.addr$0bv32$2 := $y[32:0];
    $$y.addr$1bv32$1 := $y[64:32];
    $$y.addr$1bv32$2 := $y[64:32];
    $$y.addr$2bv32$1 := $y[96:64];
    $$y.addr$2bv32$2 := $y[96:64];
    $$y.addr$3bv32$1 := 0bv32;
    $$y.addr$3bv32$2 := 0bv32;
    v0$1 := $$x.addr$0bv32$1;
    v0$2 := $$x.addr$0bv32$2;
    v1$1 := $$x.addr$1bv32$1;
    v1$2 := $$x.addr$1bv32$2;
    v2$1 := $$x.addr$2bv32$1;
    v2$2 := $$x.addr$2bv32$2;
    v3$1 := $$x.addr$3bv32$1;
    v3$2 := $$x.addr$3bv32$2;
    v4$1 := $$y.addr$0bv32$1;
    v4$2 := $$y.addr$0bv32$2;
    v5$1 := $$y.addr$1bv32$1;
    v5$2 := $$y.addr$1bv32$2;
    v6$1 := $$y.addr$2bv32$1;
    v6$2 := $$y.addr$2bv32$2;
    v7$1 := $$y.addr$3bv32$1;
    v7$2 := $$y.addr$3bv32$2;
    $$temp$0bv32$1 := FMIN32(v0$1, v4$1);
    $$temp$0bv32$2 := FMIN32(v0$2, v4$2);
    $$temp$1bv32$1 := FMIN32(v1$1, v5$1);
    $$temp$1bv32$2 := FMIN32(v1$2, v5$2);
    $$temp$2bv32$1 := FMIN32(v2$1, v6$1);
    $$temp$2bv32$2 := FMIN32(v2$2, v6$2);
    $$temp$3bv32$1 := 0bv32;
    $$temp$3bv32$2 := 0bv32;
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

var $$x.addr$0bv32$1: bv32;

var $$x.addr$0bv32$2: bv32;

var $$x.addr$1bv32$1: bv32;

var $$x.addr$1bv32$2: bv32;

var $$x.addr$2bv32$1: bv32;

var $$x.addr$2bv32$2: bv32;

var $$x.addr$3bv32$1: bv32;

var $$x.addr$3bv32$2: bv32;

var $$y.addr$0bv32$1: bv32;

var $$y.addr$0bv32$2: bv32;

var $$y.addr$1bv32$1: bv32;

var $$y.addr$1bv32$2: bv32;

var $$y.addr$2bv32$1: bv32;

var $$y.addr$2bv32$2: bv32;

var $$y.addr$3bv32$1: bv32;

var $$y.addr$3bv32$2: bv32;

var $$temp$0bv32$1: bv32;

var $$temp$0bv32$2: bv32;

var $$temp$1bv32$1: bv32;

var $$temp$1bv32$2: bv32;

var $$temp$2bv32$1: bv32;

var $$temp$2bv32$2: bv32;

var $$temp$3bv32$1: bv32;

var $$temp$3bv32$2: bv32;

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
