type ~msg_t = int;
const #funAddr~node1.base : int;
const #funAddr~node1.offset : int;
const #funAddr~node2.base : int;
const #funAddr~node2.offset : int;
const #funAddr~node3.base : int;
const #funAddr~node3.offset : int;
const #funAddr~node4.base : int;
const #funAddr~node4.offset : int;
axiom #funAddr~node1.base == -1 && #funAddr~node1.offset == 0;
axiom #funAddr~node2.base == -1 && #funAddr~node2.offset == 1;
axiom #funAddr~node3.base == -1 && #funAddr~node3.offset == 2;
axiom #funAddr~node4.base == -1 && #funAddr~node4.offset == 3;
var ~r1 : int;

var ~p1_old : int;

var ~p1_new : int;

var ~id1 : int;

var ~st1 : int;

var ~mode1 : int;

var ~p2_old : int;

var ~p2_new : int;

var ~id2 : int;

var ~st2 : int;

var ~mode2 : int;

var ~p3_old : int;

var ~p3_new : int;

var ~id3 : int;

var ~st3 : int;

var ~mode3 : int;

var ~p4_old : int;

var ~p4_new : int;

var ~id4 : int;

var ~st4 : int;

var ~mode4 : int;

var ~nomsg : ~msg_t;

var ~send1 : ~msg_t;

var ~send2 : ~msg_t;

var ~send3 : ~msg_t;

var ~send4 : ~msg_t;

implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~nondet4 : int;
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
    var main_~c1~95 : int;
    var main_~i2~95 : int;
    var init_#res : int;
    var init_~tmp~37 : int;
    var node1_#t~ite0 : int;
    var node1_~m1~7 : ~msg_t;
    var node2_#t~ite1 : int;
    var node2_~m2~16 : ~msg_t;
    var node3_#t~ite2 : int;
    var node3_~m3~23 : ~msg_t;
    var node4_#t~ite3 : int;
    var node4_~m4~30 : ~msg_t;
    var check_#res : int;
    var check_~tmp~85 : int;
    var assert_#in~arg : int;
    var assert_~arg : int;

  loc0:
    ~r1 := 0;
    ~p1_old := 0;
    ~p1_new := 0;
    ~id1 := 0;
    ~st1 := 0;
    ~mode1 := 0;
    ~p2_old := 0;
    ~p2_new := 0;
    ~id2 := 0;
    ~st2 := 0;
    ~mode2 := 0;
    ~p3_old := 0;
    ~p3_new := 0;
    ~id3 := 0;
    ~st3 := 0;
    ~mode3 := 0;
    ~p4_old := 0;
    ~p4_new := 0;
    ~id4 := 0;
    ~st4 := 0;
    ~mode4 := 0;
    ~nomsg := -1;
    ~send1 := 0;
    ~send2 := 0;
    ~send3 := 0;
    ~send4 := 0;
    havoc main_#res;
    havoc main_#t~nondet4, main_#t~nondet5, main_#t~nondet6, main_#t~nondet7, main_#t~nondet8, main_#t~nondet9, main_#t~nondet10, main_#t~nondet11, main_#t~nondet12, main_#t~nondet13, main_#t~nondet14, main_#t~nondet15, main_#t~nondet16, main_#t~nondet17, main_#t~nondet18, main_#t~nondet19, main_#t~nondet20, main_#t~ret21, main_#t~ret22, main_~c1~95, main_~i2~95;
    havoc main_~c1~95;
    havoc main_~i2~95;
    main_~c1~95 := 0;
    ~r1 := main_#t~nondet4;
    havoc main_#t~nondet4;
    assume -128 <= main_#t~nondet5 && main_#t~nondet5 <= 127;
    ~id1 := main_#t~nondet5;
    havoc main_#t~nondet5;
    assume -128 <= main_#t~nondet6 && main_#t~nondet6 <= 127;
    ~st1 := main_#t~nondet6;
    havoc main_#t~nondet6;
    assume -128 <= main_#t~nondet7 && main_#t~nondet7 <= 127;
    ~send1 := main_#t~nondet7;
    havoc main_#t~nondet7;
    ~mode1 := main_#t~nondet8;
    havoc main_#t~nondet8;
    assume -128 <= main_#t~nondet9 && main_#t~nondet9 <= 127;
    ~id2 := main_#t~nondet9;
    havoc main_#t~nondet9;
    assume -128 <= main_#t~nondet10 && main_#t~nondet10 <= 127;
    ~st2 := main_#t~nondet10;
    havoc main_#t~nondet10;
    assume -128 <= main_#t~nondet11 && main_#t~nondet11 <= 127;
    ~send2 := main_#t~nondet11;
    havoc main_#t~nondet11;
    ~mode2 := main_#t~nondet12;
    havoc main_#t~nondet12;
    assume -128 <= main_#t~nondet13 && main_#t~nondet13 <= 127;
    ~id3 := main_#t~nondet13;
    havoc main_#t~nondet13;
    assume -128 <= main_#t~nondet14 && main_#t~nondet14 <= 127;
    ~st3 := main_#t~nondet14;
    havoc main_#t~nondet14;
    assume -128 <= main_#t~nondet15 && main_#t~nondet15 <= 127;
    ~send3 := main_#t~nondet15;
    havoc main_#t~nondet15;
    ~mode3 := main_#t~nondet16;
    havoc main_#t~nondet16;
    assume -128 <= main_#t~nondet17 && main_#t~nondet17 <= 127;
    ~id4 := main_#t~nondet17;
    havoc main_#t~nondet17;
    assume -128 <= main_#t~nondet18 && main_#t~nondet18 <= 127;
    ~st4 := main_#t~nondet18;
    havoc main_#t~nondet18;
    assume -128 <= main_#t~nondet19 && main_#t~nondet19 <= 127;
    ~send4 := main_#t~nondet19;
    havoc main_#t~nondet19;
    ~mode4 := main_#t~nondet20;
    havoc main_#t~nondet20;
    havoc init_#res;
    havoc init_~tmp~37;
    havoc init_~tmp~37;
    assume ~r1 % 256 == 0;
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
    assume ~id4 >= 0;
    assume ~st4 == 0;
    assume ~send4 == ~id4;
    assume ~mode4 % 256 == 0;
    assume ~id1 != ~id2;
    assume ~id1 != ~id3;
    assume ~id1 != ~id4;
    assume ~id2 != ~id3;
    assume ~id2 != ~id4;
    assume ~id3 != ~id4;
    init_~tmp~37 := 1;
    init_#res := init_~tmp~37;
    main_#t~ret21 := init_#res;
    assume -2147483648 <= main_#t~ret21 && main_#t~ret21 <= 2147483647;
    main_~i2~95 := main_#t~ret21;
    havoc main_#t~ret21;
    assume main_~i2~95 != 0;
    ~p1_old := ~nomsg;
    ~p1_new := ~nomsg;
    ~p2_old := ~nomsg;
    ~p2_new := ~nomsg;
    ~p3_old := ~nomsg;
    ~p3_new := ~nomsg;
    ~p4_old := ~nomsg;
    ~p4_new := ~nomsg;
    main_~i2~95 := 0;
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
    assume ~mode1 % 256 != 0;
    assume !(~r1 % 256 == 255);
    ~r1 := ~r1 % 256 + 1;
    node1_~m1~7 := ~p4_old;
    ~p4_old := ~nomsg;
    assume !(node1_~m1~7 != ~nomsg);
    ~mode1 := 0;
    goto loc3;
  loc2_1:
    assume !(~mode1 % 256 != 0);
    assume ~send1 != ~nomsg && ~p1_new == ~nomsg;
    node1_#t~ite0 := ~send1;
    ~p1_new := (if node1_#t~ite0 % 256 <= 127 then node1_#t~ite0 % 256 else node1_#t~ite0 % 256 - 256);
    havoc node1_#t~ite0;
    ~mode1 := 1;
    goto loc3;
  loc3:
    havoc node2_#t~ite1, node2_~m2~16;
    havoc node2_~m2~16;
    node2_~m2~16 := ~nomsg;
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume ~mode2 % 256 != 0;
    node2_~m2~16 := ~p1_old;
    ~p1_old := ~nomsg;
    assume !(node2_~m2~16 != ~nomsg);
    ~mode2 := 0;
    goto loc5;
  loc4_1:
    assume !(~mode2 % 256 != 0);
    assume ~send2 != ~nomsg && ~p2_new == ~nomsg;
    node2_#t~ite1 := ~send2;
    ~p2_new := (if node2_#t~ite1 % 256 <= 127 then node2_#t~ite1 % 256 else node2_#t~ite1 % 256 - 256);
    havoc node2_#t~ite1;
    ~mode2 := 1;
    goto loc5;
  loc5:
    havoc node3_#t~ite2, node3_~m3~23;
    havoc node3_~m3~23;
    node3_~m3~23 := ~nomsg;
    goto loc6;
  loc6:
    goto loc6_0, loc6_1;
  loc6_0:
    assume ~mode3 % 256 != 0;
    node3_~m3~23 := ~p2_old;
    ~p2_old := ~nomsg;
    assume !(node3_~m3~23 != ~nomsg);
    ~mode3 := 0;
    goto loc7;
  loc6_1:
    assume !(~mode3 % 256 != 0);
    assume ~send3 != ~nomsg && ~p3_new == ~nomsg;
    node3_#t~ite2 := ~send3;
    ~p3_new := (if node3_#t~ite2 % 256 <= 127 then node3_#t~ite2 % 256 else node3_#t~ite2 % 256 - 256);
    havoc node3_#t~ite2;
    ~mode3 := 1;
    goto loc7;
  loc7:
    havoc node4_#t~ite3, node4_~m4~30;
    havoc node4_~m4~30;
    node4_~m4~30 := ~nomsg;
    goto loc8;
  loc8:
    goto loc8_0, loc8_1;
  loc8_0:
    assume ~mode4 % 256 != 0;
    node4_~m4~30 := ~p3_old;
    ~p3_old := ~nomsg;
    assume !(node4_~m4~30 != ~nomsg);
    ~mode4 := 0;
    goto loc9;
  loc8_1:
    assume !(~mode4 % 256 != 0);
    assume ~send4 != ~nomsg && ~p4_new == ~nomsg;
    node4_#t~ite3 := ~send4;
    ~p4_new := (if node4_#t~ite3 % 256 <= 127 then node4_#t~ite3 % 256 else node4_#t~ite3 % 256 - 256);
    havoc node4_#t~ite3;
    ~mode4 := 1;
    goto loc9;
  loc9:
    ~p1_old := ~p1_new;
    ~p1_new := ~nomsg;
    ~p2_old := ~p2_new;
    ~p2_new := ~nomsg;
    ~p3_old := ~p3_new;
    ~p3_new := ~nomsg;
    ~p4_old := ~p4_new;
    ~p4_new := ~nomsg;
    havoc check_#res;
    havoc check_~tmp~85;
    havoc check_~tmp~85;
    assume ~st1 + ~st2 + ~st3 + ~st4 <= 1;
    goto loc10;
  loc10:
    goto loc10_0, loc10_1;
  loc10_0:
    assume ~r1 % 256 >= 4;
    goto loc11;
  loc10_1:
    assume !(~r1 % 256 >= 4);
    assume ~st1 + ~st2 + ~st3 + ~st4 == 0;
    goto loc11;
  loc11:
    goto loc11_0, loc11_1;
  loc11_0:
    assume ~r1 % 256 < 4;
    check_~tmp~85 := 1;
    goto loc12;
  loc11_1:
    assume !(~r1 % 256 < 4);
    assume !(~st1 + ~st2 + ~st3 + ~st4 == 1);
    check_~tmp~85 := 0;
    goto loc12;
  loc12:
    check_#res := check_~tmp~85;
    main_#t~ret22 := check_#res;
    assume -2147483648 <= main_#t~ret22 && main_#t~ret22 <= 2147483647;
    main_~c1~95 := main_#t~ret22;
    havoc main_#t~ret22;
    assert_#in~arg := (if main_~c1~95 == 0 then 0 else 1);
    havoc assert_~arg;
    assert_~arg := assert_#in~arg;
    goto loc13;
  loc13:
    goto loc13_0, loc13_1;
  loc13_0:
    assume assert_~arg % 256 == 0;
    assume !false;
    goto loc14;
  loc13_1:
    assume !(assert_~arg % 256 == 0);
    goto loc1;
  loc14:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ~r1, ~p1_old, ~p1_new, ~id1, ~st1, ~mode1, ~p2_old, ~p2_new, ~id2, ~st2, ~mode2, ~p3_old, ~p3_new, ~id3, ~st3, ~mode3, ~p4_old, ~p4_new, ~id4, ~st4, ~mode4, ~nomsg, ~send1, ~send2, ~send3, ~send4, ~r1, ~id1, ~st1, ~send1, ~mode1, ~id2, ~st2, ~send2, ~mode2, ~id3, ~st3, ~send3, ~mode3, ~id4, ~st4, ~send4, ~mode4, ~p1_old, ~p1_new, ~p2_old, ~p2_new, ~p3_old, ~p3_new, ~p4_old, ~p4_new;
modifies ~r1, ~p4_old, ~send1, ~st1, ~mode1, ~p1_new, ~p1_old, ~send2, ~st2, ~mode2, ~p2_new, ~p2_old, ~send3, ~st3, ~mode3, ~p3_new, ~p3_old, ~send4, ~st4, ~mode4, ~p4_new, ~id1, ~id2, ~id3, ~id4;

