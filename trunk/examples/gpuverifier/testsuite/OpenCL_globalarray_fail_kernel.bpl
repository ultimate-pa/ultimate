//#Unsafe
type _SIZE_T_TYPE = bv32;

procedure _ATOMIC_OP32(x: [bv32]bv32, y: bv32) returns (z$1: bv32, A$1: [bv32]bv32, z$2: bv32, A$2: [bv32]bv32);

procedure _ATOMIC_OP8(x: [bv32]bv8, y: bv32) returns (z$1: bv8, A$1: [bv32]bv8, z$2: bv8, A$2: [bv32]bv8);

var {:source_name "p"} {:global} $$p: [bv32]bv32;

axiom {:array_info "$$p"} {:global} {:elem_width 32} {:source_name "p"} {:source_elem_width 32} {:source_dimensions "*"} true;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _READ_HAS_OCCURRED_$$p: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _WRITE_HAS_OCCURRED_$$p: bool;

var {:race_checking} {:global} {:elem_width 32} {:source_elem_width 32} {:source_dimensions "*"} _ATOMIC_HAS_OCCURRED_$$p: bool;

var {:source_name "A"} {:constant} $$A$1: [bv32]bv8;

var {:source_name "A"} {:constant} $$A$2: [bv32]bv8;

axiom {:array_info "$$A"} {:constant} {:elem_width 8} {:source_name "A"} {:source_elem_width 32} {:source_dimensions "64"} true;

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

function {:builtin "sign_extend 24"} BV8_SEXT32(bv8) : bv32;

procedure {:source_name "globalarray"} ULTIMATE.start();
  requires $$A$1[0bv32] == 0bv8;
  requires $$A$2[0bv32] == 0bv8;
  requires $$A$1[1bv32] == 0bv8;
  requires $$A$2[1bv32] == 0bv8;
  requires $$A$1[2bv32] == 0bv8;
  requires $$A$2[2bv32] == 0bv8;
  requires $$A$1[3bv32] == 0bv8;
  requires $$A$2[3bv32] == 0bv8;
  requires $$A$1[4bv32] == 0bv8;
  requires $$A$2[4bv32] == 0bv8;
  requires $$A$1[5bv32] == 0bv8;
  requires $$A$2[5bv32] == 0bv8;
  requires $$A$1[6bv32] == 0bv8;
  requires $$A$2[6bv32] == 0bv8;
  requires $$A$1[7bv32] == 0bv8;
  requires $$A$2[7bv32] == 0bv8;
  requires $$A$1[8bv32] == 0bv8;
  requires $$A$2[8bv32] == 0bv8;
  requires $$A$1[9bv32] == 0bv8;
  requires $$A$2[9bv32] == 0bv8;
  requires $$A$1[10bv32] == 0bv8;
  requires $$A$2[10bv32] == 0bv8;
  requires $$A$1[11bv32] == 0bv8;
  requires $$A$2[11bv32] == 0bv8;
  requires $$A$1[12bv32] == 0bv8;
  requires $$A$2[12bv32] == 0bv8;
  requires $$A$1[13bv32] == 0bv8;
  requires $$A$2[13bv32] == 0bv8;
  requires $$A$1[14bv32] == 0bv8;
  requires $$A$2[14bv32] == 0bv8;
  requires $$A$1[15bv32] == 0bv8;
  requires $$A$2[15bv32] == 0bv8;
  requires $$A$1[16bv32] == 0bv8;
  requires $$A$2[16bv32] == 0bv8;
  requires $$A$1[17bv32] == 0bv8;
  requires $$A$2[17bv32] == 0bv8;
  requires $$A$1[18bv32] == 0bv8;
  requires $$A$2[18bv32] == 0bv8;
  requires $$A$1[19bv32] == 0bv8;
  requires $$A$2[19bv32] == 0bv8;
  requires $$A$1[20bv32] == 0bv8;
  requires $$A$2[20bv32] == 0bv8;
  requires $$A$1[21bv32] == 0bv8;
  requires $$A$2[21bv32] == 0bv8;
  requires $$A$1[22bv32] == 0bv8;
  requires $$A$2[22bv32] == 0bv8;
  requires $$A$1[23bv32] == 0bv8;
  requires $$A$2[23bv32] == 0bv8;
  requires $$A$1[24bv32] == 0bv8;
  requires $$A$2[24bv32] == 0bv8;
  requires $$A$1[25bv32] == 0bv8;
  requires $$A$2[25bv32] == 0bv8;
  requires $$A$1[26bv32] == 0bv8;
  requires $$A$2[26bv32] == 0bv8;
  requires $$A$1[27bv32] == 0bv8;
  requires $$A$2[27bv32] == 0bv8;
  requires $$A$1[28bv32] == 0bv8;
  requires $$A$2[28bv32] == 0bv8;
  requires $$A$1[29bv32] == 0bv8;
  requires $$A$2[29bv32] == 0bv8;
  requires $$A$1[30bv32] == 0bv8;
  requires $$A$2[30bv32] == 0bv8;
  requires $$A$1[31bv32] == 0bv8;
  requires $$A$2[31bv32] == 0bv8;
  requires $$A$1[32bv32] == 0bv8;
  requires $$A$2[32bv32] == 0bv8;
  requires $$A$1[33bv32] == 0bv8;
  requires $$A$2[33bv32] == 0bv8;
  requires $$A$1[34bv32] == 0bv8;
  requires $$A$2[34bv32] == 0bv8;
  requires $$A$1[35bv32] == 0bv8;
  requires $$A$2[35bv32] == 0bv8;
  requires $$A$1[36bv32] == 0bv8;
  requires $$A$2[36bv32] == 0bv8;
  requires $$A$1[37bv32] == 0bv8;
  requires $$A$2[37bv32] == 0bv8;
  requires $$A$1[38bv32] == 0bv8;
  requires $$A$2[38bv32] == 0bv8;
  requires $$A$1[39bv32] == 0bv8;
  requires $$A$2[39bv32] == 0bv8;
  requires $$A$1[40bv32] == 0bv8;
  requires $$A$2[40bv32] == 0bv8;
  requires $$A$1[41bv32] == 0bv8;
  requires $$A$2[41bv32] == 0bv8;
  requires $$A$1[42bv32] == 0bv8;
  requires $$A$2[42bv32] == 0bv8;
  requires $$A$1[43bv32] == 0bv8;
  requires $$A$2[43bv32] == 0bv8;
  requires $$A$1[44bv32] == 0bv8;
  requires $$A$2[44bv32] == 0bv8;
  requires $$A$1[45bv32] == 0bv8;
  requires $$A$2[45bv32] == 0bv8;
  requires $$A$1[46bv32] == 0bv8;
  requires $$A$2[46bv32] == 0bv8;
  requires $$A$1[47bv32] == 0bv8;
  requires $$A$2[47bv32] == 0bv8;
  requires $$A$1[48bv32] == 0bv8;
  requires $$A$2[48bv32] == 0bv8;
  requires $$A$1[49bv32] == 0bv8;
  requires $$A$2[49bv32] == 0bv8;
  requires $$A$1[50bv32] == 0bv8;
  requires $$A$2[50bv32] == 0bv8;
  requires $$A$1[51bv32] == 0bv8;
  requires $$A$2[51bv32] == 0bv8;
  requires $$A$1[52bv32] == 0bv8;
  requires $$A$2[52bv32] == 0bv8;
  requires $$A$1[53bv32] == 0bv8;
  requires $$A$2[53bv32] == 0bv8;
  requires $$A$1[54bv32] == 0bv8;
  requires $$A$2[54bv32] == 0bv8;
  requires $$A$1[55bv32] == 0bv8;
  requires $$A$2[55bv32] == 0bv8;
  requires $$A$1[56bv32] == 0bv8;
  requires $$A$2[56bv32] == 0bv8;
  requires $$A$1[57bv32] == 0bv8;
  requires $$A$2[57bv32] == 0bv8;
  requires $$A$1[58bv32] == 0bv8;
  requires $$A$2[58bv32] == 0bv8;
  requires $$A$1[59bv32] == 0bv8;
  requires $$A$2[59bv32] == 0bv8;
  requires $$A$1[60bv32] == 0bv8;
  requires $$A$2[60bv32] == 0bv8;
  requires $$A$1[61bv32] == 0bv8;
  requires $$A$2[61bv32] == 0bv8;
  requires $$A$1[62bv32] == 0bv8;
  requires $$A$2[62bv32] == 0bv8;
  requires $$A$1[63bv32] == 0bv8;
  requires $$A$2[63bv32] == 0bv8;
  requires $$A$1[64bv32] == 0bv8;
  requires $$A$2[64bv32] == 0bv8;
  requires $$A$1[65bv32] == 0bv8;
  requires $$A$2[65bv32] == 0bv8;
  requires $$A$1[66bv32] == 0bv8;
  requires $$A$2[66bv32] == 0bv8;
  requires $$A$1[67bv32] == 0bv8;
  requires $$A$2[67bv32] == 0bv8;
  requires $$A$1[68bv32] == 0bv8;
  requires $$A$2[68bv32] == 0bv8;
  requires $$A$1[69bv32] == 0bv8;
  requires $$A$2[69bv32] == 0bv8;
  requires $$A$1[70bv32] == 0bv8;
  requires $$A$2[70bv32] == 0bv8;
  requires $$A$1[71bv32] == 0bv8;
  requires $$A$2[71bv32] == 0bv8;
  requires $$A$1[72bv32] == 0bv8;
  requires $$A$2[72bv32] == 0bv8;
  requires $$A$1[73bv32] == 0bv8;
  requires $$A$2[73bv32] == 0bv8;
  requires $$A$1[74bv32] == 0bv8;
  requires $$A$2[74bv32] == 0bv8;
  requires $$A$1[75bv32] == 0bv8;
  requires $$A$2[75bv32] == 0bv8;
  requires $$A$1[76bv32] == 0bv8;
  requires $$A$2[76bv32] == 0bv8;
  requires $$A$1[77bv32] == 0bv8;
  requires $$A$2[77bv32] == 0bv8;
  requires $$A$1[78bv32] == 0bv8;
  requires $$A$2[78bv32] == 0bv8;
  requires $$A$1[79bv32] == 0bv8;
  requires $$A$2[79bv32] == 0bv8;
  requires $$A$1[80bv32] == 0bv8;
  requires $$A$2[80bv32] == 0bv8;
  requires $$A$1[81bv32] == 0bv8;
  requires $$A$2[81bv32] == 0bv8;
  requires $$A$1[82bv32] == 0bv8;
  requires $$A$2[82bv32] == 0bv8;
  requires $$A$1[83bv32] == 0bv8;
  requires $$A$2[83bv32] == 0bv8;
  requires $$A$1[84bv32] == 0bv8;
  requires $$A$2[84bv32] == 0bv8;
  requires $$A$1[85bv32] == 0bv8;
  requires $$A$2[85bv32] == 0bv8;
  requires $$A$1[86bv32] == 0bv8;
  requires $$A$2[86bv32] == 0bv8;
  requires $$A$1[87bv32] == 0bv8;
  requires $$A$2[87bv32] == 0bv8;
  requires $$A$1[88bv32] == 0bv8;
  requires $$A$2[88bv32] == 0bv8;
  requires $$A$1[89bv32] == 0bv8;
  requires $$A$2[89bv32] == 0bv8;
  requires $$A$1[90bv32] == 0bv8;
  requires $$A$2[90bv32] == 0bv8;
  requires $$A$1[91bv32] == 0bv8;
  requires $$A$2[91bv32] == 0bv8;
  requires $$A$1[92bv32] == 0bv8;
  requires $$A$2[92bv32] == 0bv8;
  requires $$A$1[93bv32] == 0bv8;
  requires $$A$2[93bv32] == 0bv8;
  requires $$A$1[94bv32] == 0bv8;
  requires $$A$2[94bv32] == 0bv8;
  requires $$A$1[95bv32] == 0bv8;
  requires $$A$2[95bv32] == 0bv8;
  requires $$A$1[96bv32] == 0bv8;
  requires $$A$2[96bv32] == 0bv8;
  requires $$A$1[97bv32] == 0bv8;
  requires $$A$2[97bv32] == 0bv8;
  requires $$A$1[98bv32] == 0bv8;
  requires $$A$2[98bv32] == 0bv8;
  requires $$A$1[99bv32] == 0bv8;
  requires $$A$2[99bv32] == 0bv8;
  requires $$A$1[100bv32] == 0bv8;
  requires $$A$2[100bv32] == 0bv8;
  requires $$A$1[101bv32] == 0bv8;
  requires $$A$2[101bv32] == 0bv8;
  requires $$A$1[102bv32] == 0bv8;
  requires $$A$2[102bv32] == 0bv8;
  requires $$A$1[103bv32] == 0bv8;
  requires $$A$2[103bv32] == 0bv8;
  requires $$A$1[104bv32] == 0bv8;
  requires $$A$2[104bv32] == 0bv8;
  requires $$A$1[105bv32] == 0bv8;
  requires $$A$2[105bv32] == 0bv8;
  requires $$A$1[106bv32] == 0bv8;
  requires $$A$2[106bv32] == 0bv8;
  requires $$A$1[107bv32] == 0bv8;
  requires $$A$2[107bv32] == 0bv8;
  requires $$A$1[108bv32] == 0bv8;
  requires $$A$2[108bv32] == 0bv8;
  requires $$A$1[109bv32] == 0bv8;
  requires $$A$2[109bv32] == 0bv8;
  requires $$A$1[110bv32] == 0bv8;
  requires $$A$2[110bv32] == 0bv8;
  requires $$A$1[111bv32] == 0bv8;
  requires $$A$2[111bv32] == 0bv8;
  requires $$A$1[112bv32] == 0bv8;
  requires $$A$2[112bv32] == 0bv8;
  requires $$A$1[113bv32] == 0bv8;
  requires $$A$2[113bv32] == 0bv8;
  requires $$A$1[114bv32] == 0bv8;
  requires $$A$2[114bv32] == 0bv8;
  requires $$A$1[115bv32] == 0bv8;
  requires $$A$2[115bv32] == 0bv8;
  requires $$A$1[116bv32] == 0bv8;
  requires $$A$2[116bv32] == 0bv8;
  requires $$A$1[117bv32] == 0bv8;
  requires $$A$2[117bv32] == 0bv8;
  requires $$A$1[118bv32] == 0bv8;
  requires $$A$2[118bv32] == 0bv8;
  requires $$A$1[119bv32] == 0bv8;
  requires $$A$2[119bv32] == 0bv8;
  requires $$A$1[120bv32] == 0bv8;
  requires $$A$2[120bv32] == 0bv8;
  requires $$A$1[121bv32] == 0bv8;
  requires $$A$2[121bv32] == 0bv8;
  requires $$A$1[122bv32] == 0bv8;
  requires $$A$2[122bv32] == 0bv8;
  requires $$A$1[123bv32] == 0bv8;
  requires $$A$2[123bv32] == 0bv8;
  requires $$A$1[124bv32] == 0bv8;
  requires $$A$2[124bv32] == 0bv8;
  requires $$A$1[125bv32] == 0bv8;
  requires $$A$2[125bv32] == 0bv8;
  requires $$A$1[126bv32] == 0bv8;
  requires $$A$2[126bv32] == 0bv8;
  requires $$A$1[127bv32] == 0bv8;
  requires $$A$2[127bv32] == 0bv8;
  requires $$A$1[128bv32] == 0bv8;
  requires $$A$2[128bv32] == 0bv8;
  requires $$A$1[129bv32] == 0bv8;
  requires $$A$2[129bv32] == 0bv8;
  requires $$A$1[130bv32] == 0bv8;
  requires $$A$2[130bv32] == 0bv8;
  requires $$A$1[131bv32] == 0bv8;
  requires $$A$2[131bv32] == 0bv8;
  requires $$A$1[132bv32] == 0bv8;
  requires $$A$2[132bv32] == 0bv8;
  requires $$A$1[133bv32] == 0bv8;
  requires $$A$2[133bv32] == 0bv8;
  requires $$A$1[134bv32] == 0bv8;
  requires $$A$2[134bv32] == 0bv8;
  requires $$A$1[135bv32] == 0bv8;
  requires $$A$2[135bv32] == 0bv8;
  requires $$A$1[136bv32] == 0bv8;
  requires $$A$2[136bv32] == 0bv8;
  requires $$A$1[137bv32] == 0bv8;
  requires $$A$2[137bv32] == 0bv8;
  requires $$A$1[138bv32] == 0bv8;
  requires $$A$2[138bv32] == 0bv8;
  requires $$A$1[139bv32] == 0bv8;
  requires $$A$2[139bv32] == 0bv8;
  requires $$A$1[140bv32] == 0bv8;
  requires $$A$2[140bv32] == 0bv8;
  requires $$A$1[141bv32] == 0bv8;
  requires $$A$2[141bv32] == 0bv8;
  requires $$A$1[142bv32] == 0bv8;
  requires $$A$2[142bv32] == 0bv8;
  requires $$A$1[143bv32] == 0bv8;
  requires $$A$2[143bv32] == 0bv8;
  requires $$A$1[144bv32] == 0bv8;
  requires $$A$2[144bv32] == 0bv8;
  requires $$A$1[145bv32] == 0bv8;
  requires $$A$2[145bv32] == 0bv8;
  requires $$A$1[146bv32] == 0bv8;
  requires $$A$2[146bv32] == 0bv8;
  requires $$A$1[147bv32] == 0bv8;
  requires $$A$2[147bv32] == 0bv8;
  requires $$A$1[148bv32] == 0bv8;
  requires $$A$2[148bv32] == 0bv8;
  requires $$A$1[149bv32] == 0bv8;
  requires $$A$2[149bv32] == 0bv8;
  requires $$A$1[150bv32] == 0bv8;
  requires $$A$2[150bv32] == 0bv8;
  requires $$A$1[151bv32] == 0bv8;
  requires $$A$2[151bv32] == 0bv8;
  requires $$A$1[152bv32] == 0bv8;
  requires $$A$2[152bv32] == 0bv8;
  requires $$A$1[153bv32] == 0bv8;
  requires $$A$2[153bv32] == 0bv8;
  requires $$A$1[154bv32] == 0bv8;
  requires $$A$2[154bv32] == 0bv8;
  requires $$A$1[155bv32] == 0bv8;
  requires $$A$2[155bv32] == 0bv8;
  requires $$A$1[156bv32] == 0bv8;
  requires $$A$2[156bv32] == 0bv8;
  requires $$A$1[157bv32] == 0bv8;
  requires $$A$2[157bv32] == 0bv8;
  requires $$A$1[158bv32] == 0bv8;
  requires $$A$2[158bv32] == 0bv8;
  requires $$A$1[159bv32] == 0bv8;
  requires $$A$2[159bv32] == 0bv8;
  requires $$A$1[160bv32] == 0bv8;
  requires $$A$2[160bv32] == 0bv8;
  requires $$A$1[161bv32] == 0bv8;
  requires $$A$2[161bv32] == 0bv8;
  requires $$A$1[162bv32] == 0bv8;
  requires $$A$2[162bv32] == 0bv8;
  requires $$A$1[163bv32] == 0bv8;
  requires $$A$2[163bv32] == 0bv8;
  requires $$A$1[164bv32] == 0bv8;
  requires $$A$2[164bv32] == 0bv8;
  requires $$A$1[165bv32] == 0bv8;
  requires $$A$2[165bv32] == 0bv8;
  requires $$A$1[166bv32] == 0bv8;
  requires $$A$2[166bv32] == 0bv8;
  requires $$A$1[167bv32] == 0bv8;
  requires $$A$2[167bv32] == 0bv8;
  requires $$A$1[168bv32] == 0bv8;
  requires $$A$2[168bv32] == 0bv8;
  requires $$A$1[169bv32] == 0bv8;
  requires $$A$2[169bv32] == 0bv8;
  requires $$A$1[170bv32] == 0bv8;
  requires $$A$2[170bv32] == 0bv8;
  requires $$A$1[171bv32] == 0bv8;
  requires $$A$2[171bv32] == 0bv8;
  requires $$A$1[172bv32] == 0bv8;
  requires $$A$2[172bv32] == 0bv8;
  requires $$A$1[173bv32] == 0bv8;
  requires $$A$2[173bv32] == 0bv8;
  requires $$A$1[174bv32] == 0bv8;
  requires $$A$2[174bv32] == 0bv8;
  requires $$A$1[175bv32] == 0bv8;
  requires $$A$2[175bv32] == 0bv8;
  requires $$A$1[176bv32] == 0bv8;
  requires $$A$2[176bv32] == 0bv8;
  requires $$A$1[177bv32] == 0bv8;
  requires $$A$2[177bv32] == 0bv8;
  requires $$A$1[178bv32] == 0bv8;
  requires $$A$2[178bv32] == 0bv8;
  requires $$A$1[179bv32] == 0bv8;
  requires $$A$2[179bv32] == 0bv8;
  requires $$A$1[180bv32] == 0bv8;
  requires $$A$2[180bv32] == 0bv8;
  requires $$A$1[181bv32] == 0bv8;
  requires $$A$2[181bv32] == 0bv8;
  requires $$A$1[182bv32] == 0bv8;
  requires $$A$2[182bv32] == 0bv8;
  requires $$A$1[183bv32] == 0bv8;
  requires $$A$2[183bv32] == 0bv8;
  requires $$A$1[184bv32] == 0bv8;
  requires $$A$2[184bv32] == 0bv8;
  requires $$A$1[185bv32] == 0bv8;
  requires $$A$2[185bv32] == 0bv8;
  requires $$A$1[186bv32] == 0bv8;
  requires $$A$2[186bv32] == 0bv8;
  requires $$A$1[187bv32] == 0bv8;
  requires $$A$2[187bv32] == 0bv8;
  requires $$A$1[188bv32] == 0bv8;
  requires $$A$2[188bv32] == 0bv8;
  requires $$A$1[189bv32] == 0bv8;
  requires $$A$2[189bv32] == 0bv8;
  requires $$A$1[190bv32] == 0bv8;
  requires $$A$2[190bv32] == 0bv8;
  requires $$A$1[191bv32] == 0bv8;
  requires $$A$2[191bv32] == 0bv8;
  requires $$A$1[192bv32] == 0bv8;
  requires $$A$2[192bv32] == 0bv8;
  requires $$A$1[193bv32] == 0bv8;
  requires $$A$2[193bv32] == 0bv8;
  requires $$A$1[194bv32] == 0bv8;
  requires $$A$2[194bv32] == 0bv8;
  requires $$A$1[195bv32] == 0bv8;
  requires $$A$2[195bv32] == 0bv8;
  requires $$A$1[196bv32] == 0bv8;
  requires $$A$2[196bv32] == 0bv8;
  requires $$A$1[197bv32] == 0bv8;
  requires $$A$2[197bv32] == 0bv8;
  requires $$A$1[198bv32] == 0bv8;
  requires $$A$2[198bv32] == 0bv8;
  requires $$A$1[199bv32] == 0bv8;
  requires $$A$2[199bv32] == 0bv8;
  requires $$A$1[200bv32] == 0bv8;
  requires $$A$2[200bv32] == 0bv8;
  requires $$A$1[201bv32] == 0bv8;
  requires $$A$2[201bv32] == 0bv8;
  requires $$A$1[202bv32] == 0bv8;
  requires $$A$2[202bv32] == 0bv8;
  requires $$A$1[203bv32] == 0bv8;
  requires $$A$2[203bv32] == 0bv8;
  requires $$A$1[204bv32] == 0bv8;
  requires $$A$2[204bv32] == 0bv8;
  requires $$A$1[205bv32] == 0bv8;
  requires $$A$2[205bv32] == 0bv8;
  requires $$A$1[206bv32] == 0bv8;
  requires $$A$2[206bv32] == 0bv8;
  requires $$A$1[207bv32] == 0bv8;
  requires $$A$2[207bv32] == 0bv8;
  requires $$A$1[208bv32] == 0bv8;
  requires $$A$2[208bv32] == 0bv8;
  requires $$A$1[209bv32] == 0bv8;
  requires $$A$2[209bv32] == 0bv8;
  requires $$A$1[210bv32] == 0bv8;
  requires $$A$2[210bv32] == 0bv8;
  requires $$A$1[211bv32] == 0bv8;
  requires $$A$2[211bv32] == 0bv8;
  requires $$A$1[212bv32] == 0bv8;
  requires $$A$2[212bv32] == 0bv8;
  requires $$A$1[213bv32] == 0bv8;
  requires $$A$2[213bv32] == 0bv8;
  requires $$A$1[214bv32] == 0bv8;
  requires $$A$2[214bv32] == 0bv8;
  requires $$A$1[215bv32] == 0bv8;
  requires $$A$2[215bv32] == 0bv8;
  requires $$A$1[216bv32] == 0bv8;
  requires $$A$2[216bv32] == 0bv8;
  requires $$A$1[217bv32] == 0bv8;
  requires $$A$2[217bv32] == 0bv8;
  requires $$A$1[218bv32] == 0bv8;
  requires $$A$2[218bv32] == 0bv8;
  requires $$A$1[219bv32] == 0bv8;
  requires $$A$2[219bv32] == 0bv8;
  requires $$A$1[220bv32] == 0bv8;
  requires $$A$2[220bv32] == 0bv8;
  requires $$A$1[221bv32] == 0bv8;
  requires $$A$2[221bv32] == 0bv8;
  requires $$A$1[222bv32] == 0bv8;
  requires $$A$2[222bv32] == 0bv8;
  requires $$A$1[223bv32] == 0bv8;
  requires $$A$2[223bv32] == 0bv8;
  requires $$A$1[224bv32] == 0bv8;
  requires $$A$2[224bv32] == 0bv8;
  requires $$A$1[225bv32] == 0bv8;
  requires $$A$2[225bv32] == 0bv8;
  requires $$A$1[226bv32] == 0bv8;
  requires $$A$2[226bv32] == 0bv8;
  requires $$A$1[227bv32] == 0bv8;
  requires $$A$2[227bv32] == 0bv8;
  requires $$A$1[228bv32] == 0bv8;
  requires $$A$2[228bv32] == 0bv8;
  requires $$A$1[229bv32] == 0bv8;
  requires $$A$2[229bv32] == 0bv8;
  requires $$A$1[230bv32] == 0bv8;
  requires $$A$2[230bv32] == 0bv8;
  requires $$A$1[231bv32] == 0bv8;
  requires $$A$2[231bv32] == 0bv8;
  requires $$A$1[232bv32] == 0bv8;
  requires $$A$2[232bv32] == 0bv8;
  requires $$A$1[233bv32] == 0bv8;
  requires $$A$2[233bv32] == 0bv8;
  requires $$A$1[234bv32] == 0bv8;
  requires $$A$2[234bv32] == 0bv8;
  requires $$A$1[235bv32] == 0bv8;
  requires $$A$2[235bv32] == 0bv8;
  requires $$A$1[236bv32] == 0bv8;
  requires $$A$2[236bv32] == 0bv8;
  requires $$A$1[237bv32] == 0bv8;
  requires $$A$2[237bv32] == 0bv8;
  requires $$A$1[238bv32] == 0bv8;
  requires $$A$2[238bv32] == 0bv8;
  requires $$A$1[239bv32] == 0bv8;
  requires $$A$2[239bv32] == 0bv8;
  requires $$A$1[240bv32] == 0bv8;
  requires $$A$2[240bv32] == 0bv8;
  requires $$A$1[241bv32] == 0bv8;
  requires $$A$2[241bv32] == 0bv8;
  requires $$A$1[242bv32] == 0bv8;
  requires $$A$2[242bv32] == 0bv8;
  requires $$A$1[243bv32] == 0bv8;
  requires $$A$2[243bv32] == 0bv8;
  requires $$A$1[244bv32] == 0bv8;
  requires $$A$2[244bv32] == 0bv8;
  requires $$A$1[245bv32] == 0bv8;
  requires $$A$2[245bv32] == 0bv8;
  requires $$A$1[246bv32] == 0bv8;
  requires $$A$2[246bv32] == 0bv8;
  requires $$A$1[247bv32] == 0bv8;
  requires $$A$2[247bv32] == 0bv8;
  requires $$A$1[248bv32] == 0bv8;
  requires $$A$2[248bv32] == 0bv8;
  requires $$A$1[249bv32] == 0bv8;
  requires $$A$2[249bv32] == 0bv8;
  requires $$A$1[250bv32] == 0bv8;
  requires $$A$2[250bv32] == 0bv8;
  requires $$A$1[251bv32] == 0bv8;
  requires $$A$2[251bv32] == 0bv8;
  requires $$A$1[252bv32] == 0bv8;
  requires $$A$2[252bv32] == 0bv8;
  requires $$A$1[253bv32] == 0bv8;
  requires $$A$2[253bv32] == 0bv8;
  requires $$A$1[254bv32] == 0bv8;
  requires $$A$2[254bv32] == 0bv8;
  requires $$A$1[255bv32] == 0bv8;
  requires $$A$2[255bv32] == 0bv8;
  requires !_READ_HAS_OCCURRED_$$p && !_WRITE_HAS_OCCURRED_$$p && !_ATOMIC_HAS_OCCURRED_$$p;
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
  modifies _WRITE_HAS_OCCURRED_$$p, _WRITE_READ_BENIGN_FLAG_$$p, _WRITE_READ_BENIGN_FLAG_$$p;

implementation {:source_name "globalarray"} ULTIMATE.start()
{
  var v0$1: bv8;
  var v0$2: bv8;
  var v1$1: bv8;
  var v1$2: bv8;
  var v2$1: bv8;
  var v2$2: bv8;
  var v3$1: bv8;
  var v3$2: bv8;
  var v5$1: bool;
  var v5$2: bool;
  var v4$1: bv8;
  var v4$2: bv8;
  var p0$1: bool;
  var p0$2: bool;
  var p1$1: bool;
  var p1$2: bool;

  $entry:
    v0$1 := $$A$1[BV32_MUL(BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32), 4bv32)];
    v0$2 := $$A$2[BV32_MUL(BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32), 4bv32)];
    v1$1 := $$A$1[BV32_ADD(BV32_MUL(BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32), 4bv32), 1bv32)];
    v1$2 := $$A$2[BV32_ADD(BV32_MUL(BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32), 4bv32), 1bv32)];
    v2$1 := $$A$1[BV32_ADD(BV32_MUL(BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32), 4bv32), 2bv32)];
    v2$2 := $$A$2[BV32_ADD(BV32_MUL(BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32), 4bv32), 2bv32)];
    v3$1 := $$A$1[BV32_ADD(BV32_MUL(BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), 1bv32), 4bv32), 3bv32)];
    v3$2 := $$A$2[BV32_ADD(BV32_MUL(BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), 1bv32), 4bv32), 3bv32)];
    v4$1 := $$A$1[0bv32];
    v4$2 := $$A$2[0bv32];
    v5$1 := v3$1 ++ v2$1 ++ v1$1 ++ v0$1 == 0bv32;
    v5$2 := v3$2 ++ v2$2 ++ v1$2 ++ v0$2 == 0bv32;
    p0$1 := false;
    p0$2 := false;
    p1$1 := false;
    p1$2 := false;
    p0$1 := (if v5$1 then v5$1 else p0$1);
    p0$2 := (if v5$2 then v5$2 else p0$2);
    call _LOG_WRITE_$$p(p0$1, 0bv32, UI32_TO_FP32(BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), BV8_SEXT32(v4$1))), $$p[0bv32]);
    call _UPDATE_WRITE_READ_BENIGN_FLAG_$$p(p0$2, 0bv32);
    assume {:do_not_predicate} {:check_id "check_state_0"} {:captureState "check_state_0"} {:sourceloc} {:sourceloc_num 7} true;
    call _CHECK_WRITE_$$p(p0$2, 0bv32, UI32_TO_FP32(BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), BV8_SEXT32(v4$2))));
    assume {:captureState "call_return_state_0"} {:procedureName "_CHECK_WRITE_$$p"} true;
    $$p[0bv32] := (if p0$1 then UI32_TO_FP32(BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$1, group_size_x), local_id_x$1), BV8_SEXT32(v4$1))) else $$p[0bv32]);
    $$p[0bv32] := (if p0$2 then UI32_TO_FP32(BV32_ADD(BV32_ADD(BV32_MUL(group_id_x$2, group_size_x), local_id_x$2), BV8_SEXT32(v4$2))) else $$p[0bv32]);
    return;
}

axiom (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_z == 1bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if group_size_x == 8bv32 then 1bv1 else 0bv1) != 0bv1;

axiom (if num_groups_x == 8bv32 then 1bv1 else 0bv1) != 0bv1;

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

var _TRACKING: bool;

function {:builtin "bvsgt"} BV32_SGT(bv32, bv32) : bool;

function {:builtin "bvsge"} BV32_SGE(bv32, bv32) : bool;

function {:builtin "bvslt"} BV32_SLT(bv32, bv32) : bool;
