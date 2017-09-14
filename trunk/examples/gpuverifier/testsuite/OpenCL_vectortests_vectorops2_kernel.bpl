//#Safe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP8(x: [bv32]bv8, y: bv32) returns (z$1: bv8, A$1: [bv32]bv8, z$2: bv8, A$2: [bv32]bv8);

axiom {:array_info "$$v"} {:elem_width 8} {:source_name "v"} {:source_elem_width 32} {:source_dimensions "1"} true;

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

function {:builtin "bvand"} BV8_AND(bv8, bv8) : bv8;

function {:builtin "bvshl"} BV8_SHL(bv8, bv8) : bv8;

function {:builtin "bvxor"} BV8_XOR(bv8, bv8) : bv8;

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
  var v0$1: bv8;
  var v0$2: bv8;
  var v1$1: bv24;
  var v1$2: bv24;
  var v2$1: bv8;
  var v2$2: bv8;
  var v3$1: bv8;
  var v3$2: bv8;
  var v4$1: bv8;
  var v4$2: bv8;
  var v5$1: bv8;
  var v5$2: bv8;
  var v6$1: bv8;
  var v6$2: bv8;
  var v7$1: bv8;
  var v7$2: bv8;
  var v8$1: bv8;
  var v8$2: bv8;
  var v9$1: bv8;
  var v9$2: bv8;
  var v11$1: bv8;
  var v11$2: bv8;
  var v12$1: bv8;
  var v12$2: bv8;
  var v10$1: bv8;
  var v10$2: bv8;
  var v13$1: bv8;
  var v13$2: bv8;
  var v14$1: bv8;
  var v14$2: bv8;
  var v15$1: bv8;
  var v15$2: bv8;
  var v16$1: bv8;
  var v16$2: bv8;
  var v17$1: bv8;
  var v17$2: bv8;

  $entry:
    call v0$1, v0$2 := $bar();
    assume {:captureState "call_return_state_0"} {:procedureName "$bar"} true;
    call v1$1, v1$2 := $baz();
    assume {:captureState "call_return_state_0"} {:procedureName "$baz"} true;
    $$v$0bv32$1 := v1$1[8:0];
    $$v$0bv32$2 := v1$2[8:0];
    $$v$1bv32$1 := v1$1[16:8];
    $$v$1bv32$2 := v1$2[16:8];
    $$v$2bv32$1 := v1$1[24:16];
    $$v$2bv32$2 := v1$2[24:16];
    $$v$3bv32$1 := 0bv8;
    $$v$3bv32$2 := 0bv8;
    v2$1 := $$v$0bv32$1;
    v2$2 := $$v$0bv32$2;
    v3$1 := $$v$1bv32$1;
    v3$2 := $$v$1bv32$2;
    v4$1 := $$v$2bv32$1;
    v4$2 := $$v$2bv32$2;
    v5$1 := $$v$3bv32$1;
    v5$2 := $$v$3bv32$2;
    v6$1 := $$v$0bv32$1;
    v6$2 := $$v$0bv32$2;
    v7$1 := $$v$1bv32$1;
    v7$2 := $$v$1bv32$2;
    v8$1 := $$v$2bv32$1;
    v8$2 := $$v$2bv32$2;
    v9$1 := $$v$3bv32$1;
    v9$2 := $$v$3bv32$2;
    $$v$0bv32$1 := BV8_SHL(v6$1, BV8_AND(v2$1, 7bv8));
    $$v$0bv32$2 := BV8_SHL(v6$2, BV8_AND(v2$2, 7bv8));
    $$v$1bv32$1 := BV8_SHL(v7$1, BV8_AND(v3$1, 7bv8));
    $$v$1bv32$2 := BV8_SHL(v7$2, BV8_AND(v3$2, 7bv8));
    $$v$2bv32$1 := BV8_SHL(v8$1, BV8_AND(v4$1, 7bv8));
    $$v$2bv32$2 := BV8_SHL(v8$2, BV8_AND(v4$2, 7bv8));
    $$v$3bv32$1 := 0bv8;
    $$v$3bv32$2 := 0bv8;
    v10$1 := $$v$0bv32$1;
    v10$2 := $$v$0bv32$2;
    v11$1 := $$v$1bv32$1;
    v11$2 := $$v$1bv32$2;
    v12$1 := $$v$2bv32$1;
    v12$2 := $$v$2bv32$2;
    v13$1 := $$v$3bv32$1;
    v13$2 := $$v$3bv32$2;
    v14$1 := $$v$0bv32$1;
    v14$2 := $$v$0bv32$2;
    v15$1 := $$v$1bv32$1;
    v15$2 := $$v$1bv32$2;
    v16$1 := $$v$2bv32$1;
    v16$2 := $$v$2bv32$2;
    v17$1 := $$v$3bv32$1;
    v17$2 := $$v$3bv32$2;
    $$v$0bv32$1 := BV8_XOR(v10$1, v14$1);
    $$v$0bv32$2 := BV8_XOR(v10$2, v14$2);
    $$v$1bv32$1 := BV8_XOR(v11$1, v15$1);
    $$v$1bv32$2 := BV8_XOR(v11$2, v15$2);
    $$v$2bv32$1 := BV8_XOR(v12$1, v16$1);
    $$v$2bv32$2 := BV8_XOR(v12$2, v16$2);
    $$v$3bv32$1 := 0bv8;
    $$v$3bv32$2 := 0bv8;
    return;
}

procedure {:source_name "bar"} $bar() returns ($ret$1: bv8, $ret$2: bv8);

procedure {:source_name "baz"} $baz() returns ($ret$1: bv24, $ret$2: bv24);

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

var $$v$0bv32$1: bv8;

var $$v$0bv32$2: bv8;

var $$v$1bv32$1: bv8;

var $$v$1bv32$2: bv8;

var $$v$2bv32$1: bv8;

var $$v$2bv32$2: bv8;

var $$v$3bv32$1: bv8;

var $$v$3bv32$2: bv8;

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
