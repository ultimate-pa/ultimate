type ~msg_t = int;
const #funAddr~node1.base : int;
const #funAddr~node1.offset : int;
const #funAddr~node2.base : int;
const #funAddr~node2.offset : int;
const #funAddr~node3.base : int;
const #funAddr~node3.offset : int;
axiom #funAddr~node1.base == -1 && #funAddr~node1.offset == 0;
axiom #funAddr~node2.base == -1 && #funAddr~node2.offset == 1;
axiom #funAddr~node3.base == -1 && #funAddr~node3.offset == 2;
var ~r1 : int;

var ~p1_old : int;

var ~p1_new : int;

var ~id1 : int;

var ~st1 : int;

var ~mode1 : int;

var ~alive1 : int;

var ~p2_old : int;

var ~p2_new : int;

var ~id2 : int;

var ~st2 : int;

var ~mode2 : int;

var ~alive2 : int;

var ~p3_old : int;

var ~p3_new : int;

var ~id3 : int;

var ~st3 : int;

var ~mode3 : int;

var ~alive3 : int;

var ~nomsg : ~msg_t;

var ~send1 : ~msg_t;

var ~send2 : ~msg_t;

var ~send3 : ~msg_t;

implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~nondet5 : int;
    var main_#t~nondet6 : int;
    var main_#t~nondet7 : int;
    var main_#t~nondet8 : int;
    var main_#t~nondet9 : int;
    var main_#t~nondet10 : int;
    var main_#t~nondet11 : int;
    var main_#t~nondet12 : int;
    var main_#t~nondet13 : int;
    var main_#t~nondet14 : int;
    var main_#t~nondet15 : int;
    var main_#t~nondet16 : int;
    var main_#t~nondet17 : int;
    var main_#t~nondet18 : int;
    var main_#t~nondet19 : int;
    var main_#t~nondet20 : int;
    var main_#t~ret21 : int;
    var main_#t~ret22 : int;
    var main_~c1~83 : int;
    var main_~i2~83 : int;
    var init_#res : int;
    var init_~tmp~40 : int;
    var node1_#t~ite0 : int;
    var node1_~m1~7 : ~msg_t;
    var node2_#t~ite1 : int;
    var node2_#t~ite2 : int;
    var node2_~m2~18 : ~msg_t;
    var node3_#t~ite3 : int;
    var node3_#t~ite4 : int;
    var node3_~m3~29 : ~msg_t;
    var check_#res : int;
    var check_~tmp~76 : int;
    var assert_#in~arg : int;
    var assert_~arg : int;

  loc0:
    ~r1 := 0;
    ~p1_old := 0;
    ~p1_new := 0;
    ~id1 := 0;
    ~st1 := 0;
    ~mode1 := 0;
    ~alive1 := 0;
    ~p2_old := 0;
    ~p2_new := 0;
    ~id2 := 0;
    ~st2 := 0;
    ~mode2 := 0;
    ~alive2 := 0;
    ~p3_old := 0;
    ~p3_new := 0;
    ~id3 := 0;
    ~st3 := 0;
    ~mode3 := 0;
    ~alive3 := 0;
    ~nomsg := -1;
    ~send1 := 0;
    ~send2 := 0;
    ~send3 := 0;
    havoc main_#res;
    havoc main_#t~nondet5, main_#t~nondet6, main_#t~nondet7, main_#t~nondet8, main_#t~nondet9, main_#t~nondet10, main_#t~nondet11, main_#t~nondet12, main_#t~nondet13, main_#t~nondet14, main_#t~nondet15, main_#t~nondet16, main_#t~nondet17, main_#t~nondet18, main_#t~nondet19, main_#t~nondet20, main_#t~ret21, main_#t~ret22, main_~c1~83, main_~i2~83;
    havoc main_~c1~83;
    havoc main_~i2~83;
    main_~c1~83 := 0;
    ~r1 := main_#t~nondet5;
    havoc main_#t~nondet5;
    assume -128 <= main_#t~nondet6 && main_#t~nondet6 <= 127;
    ~id1 := main_#t~nondet6;
    havoc main_#t~nondet6;
    assume -128 <= main_#t~nondet7 && main_#t~nondet7 <= 127;
    ~st1 := main_#t~nondet7;
    havoc main_#t~nondet7;
    assume -128 <= main_#t~nondet8 && main_#t~nondet8 <= 127;
    ~send1 := main_#t~nondet8;
    havoc main_#t~nondet8;
    ~mode1 := main_#t~nondet9;
    havoc main_#t~nondet9;
    ~alive1 := main_#t~nondet10;
    havoc main_#t~nondet10;
    assume -128 <= main_#t~nondet11 && main_#t~nondet11 <= 127;
    ~id2 := main_#t~nondet11;
    havoc main_#t~nondet11;
    assume -128 <= main_#t~nondet12 && main_#t~nondet12 <= 127;
    ~st2 := main_#t~nondet12;
    havoc main_#t~nondet12;
    assume -128 <= main_#t~nondet13 && main_#t~nondet13 <= 127;
    ~send2 := main_#t~nondet13;
    havoc main_#t~nondet13;
    ~mode2 := main_#t~nondet14;
    havoc main_#t~nondet14;
    ~alive2 := main_#t~nondet15;
    havoc main_#t~nondet15;
    assume -128 <= main_#t~nondet16 && main_#t~nondet16 <= 127;
    ~id3 := main_#t~nondet16;
    havoc main_#t~nondet16;
    assume -128 <= main_#t~nondet17 && main_#t~nondet17 <= 127;
    ~st3 := main_#t~nondet17;
    havoc main_#t~nondet17;
    assume -128 <= main_#t~nondet18 && main_#t~nondet18 <= 127;
    ~send3 := main_#t~nondet18;
    havoc main_#t~nondet18;
    ~mode3 := main_#t~nondet19;
    havoc main_#t~nondet19;
    ~alive3 := main_#t~nondet20;
    havoc main_#t~nondet20;
    havoc init_#res;
    havoc init_~tmp~40;
    havoc init_~tmp~40;
    assume ~r1 % 256 == 0;
    assume ~alive1 % 256 + ~alive2 % 256 + ~alive3 % 256 >= 1;
    assume ~id1 >= 0;
    assume ~st1 == 0;
    assume ~send1 == ~id1;
    assume ~mode1 % 256 == 0;
    assume ~id2 >= 0;
    assume ~st2 == 0;
    assume ~send2 == ~id2;
    assume ~mode2 % 256 == 0;
    assume ~id3 >= 0;
    assume ~st3 == 0;
    assume ~send3 == ~id3;
    assume ~mode3 % 256 == 0;
    assume ~id1 != ~id2;
    assume ~id1 != ~id3;
    assume ~id2 != ~id3;
    init_~tmp~40 := 1;
    init_#res := init_~tmp~40;
    main_#t~ret21 := init_#res;
    assume -2147483648 <= main_#t~ret21 && main_#t~ret21 <= 2147483647;
    main_~i2~83 := main_#t~ret21;
    havoc main_#t~ret21;
    assume main_~i2~83 != 0;
    ~p1_old := ~nomsg;
    ~p1_new := ~nomsg;
    ~p2_old := ~nomsg;
    ~p2_new := ~nomsg;
    ~p3_old := ~nomsg;
    ~p3_new := ~nomsg;
    main_~i2~83 := 0;
    goto loc1;
  loc1:
    assume true;
    assume !false;
    havoc node1_#t~ite0, node1_~m1~7;
    havoc node1_~m1~7;
    node1_~m1~7 := ~nomsg;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(~mode1 % 256 != 0);
    assume !(~alive1 % 256 != 0);
    ~mode1 := 1;
    goto loc3;
  loc2_1:
    assume ~mode1 % 256 != 0;
    assume !(~r1 % 256 == 255);
    ~r1 := ~r1 % 256 + 1;
    node1_~m1~7 := ~p3_old;
    ~p3_old := ~nomsg;
    assume !(node1_~m1~7 != ~nomsg);
    ~mode1 := 0;
    goto loc3;
  loc3:
    havoc node2_#t~ite1, node2_#t~ite2, node2_~m2~18;
    havoc node2_~m2~18;
    node2_~m2~18 := ~nomsg;
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume ~mode2 % 256 != 0;
    node2_~m2~18 := ~p1_old;
    ~p1_old := ~nomsg;
    assume !(node2_~m2~18 != ~nomsg);
    ~mode2 := 0;
    goto loc5;
  loc4_1:
    assume !(~mode2 % 256 != 0);
    assume !(~alive2 % 256 != 0);
    assume !(~send2 != ~id2);
    ~mode2 := 1;
    goto loc5;
  loc5:
    havoc node3_#t~ite3, node3_#t~ite4, node3_~m3~29;
    havoc node3_~m3~29;
    node3_~m3~29 := ~nomsg;
    goto loc6;
  loc6:
    goto loc6_0, loc6_1;
  loc6_0:
    assume !(~mode3 % 256 != 0);
    assume ~alive3 % 256 != 0;
    assume ~send3 != ~nomsg && ~p3_new == ~nomsg;
    node3_#t~ite3 := ~send3;
    ~p3_new := (if node3_#t~ite3 % 256 <= 127 then node3_#t~ite3 % 256 else node3_#t~ite3 % 256 - 256);
    havoc node3_#t~ite3;
    ~mode3 := 1;
    goto loc7;
  loc6_1:
    assume ~mode3 % 256 != 0;
    node3_~m3~29 := ~p2_old;
    ~p2_old := ~nomsg;
    assume !(node3_~m3~29 != ~nomsg);
    ~mode3 := 0;
    goto loc7;
  loc7:
    ~p1_old := ~p1_new;
    ~p1_new := ~nomsg;
    ~p2_old := ~p2_new;
    ~p2_new := ~nomsg;
    ~p3_old := ~p3_new;
    ~p3_new := ~nomsg;
    havoc check_#res;
    havoc check_~tmp~76;
    havoc check_~tmp~76;
    assume ~st1 + ~st2 + ~st3 <= 1;
    goto loc8;
  loc8:
    goto loc8_0, loc8_1;
  loc8_0:
    assume ~r1 % 256 < 3;
    check_~tmp~76 := 1;
    goto loc9;
  loc8_1:
    assume !(~r1 % 256 < 3);
    assume !(~st1 + ~st2 + ~st3 == 1);
    check_~tmp~76 := 0;
    goto loc9;
  loc9:
    check_#res := check_~tmp~76;
    main_#t~ret22 := check_#res;
    assume -2147483648 <= main_#t~ret22 && main_#t~ret22 <= 2147483647;
    main_~c1~83 := main_#t~ret22;
    havoc main_#t~ret22;
    assert_#in~arg := (if main_~c1~83 == 0 then 0 else 1);
    havoc assert_~arg;
    assert_~arg := assert_#in~arg;
    goto loc10;
  loc10:
    goto loc10_0, loc10_1;
  loc10_0:
    assume assert_~arg % 256 == 0;
    assume !false;
    goto loc11;
  loc10_1:
    assume !(assert_~arg % 256 == 0);
    goto loc1;
  loc11:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ~r1, ~p1_old, ~p1_new, ~id1, ~st1, ~mode1, ~alive1, ~p2_old, ~p2_new, ~id2, ~st2, ~mode2, ~alive2, ~p3_old, ~p3_new, ~id3, ~st3, ~mode3, ~alive3, ~nomsg, ~send1, ~send2, ~send3, ~r1, ~id1, ~st1, ~send1, ~mode1, ~alive1, ~id2, ~st2, ~send2, ~mode2, ~alive2, ~id3, ~st3, ~send3, ~mode3, ~alive3, ~p1_old, ~p1_new, ~p2_old, ~p2_new, ~p3_old, ~p3_new;
modifies ~r1, ~p3_old, ~send1, ~st1, ~mode1, ~p1_new, ~p1_old, ~send2, ~st2, ~mode2, ~p2_new, ~p2_old, ~send3, ~st3, ~mode3, ~p3_new, ~id1, ~alive1, ~id2, ~alive2, ~id3, ~alive3;

