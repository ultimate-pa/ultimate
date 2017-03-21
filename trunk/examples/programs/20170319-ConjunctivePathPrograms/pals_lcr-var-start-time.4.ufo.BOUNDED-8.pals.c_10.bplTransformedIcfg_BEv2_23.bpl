var ~send4 : int;

var ~alive2 : int;

var ~send2 : int;

var ~p4_new : int;

var ~id4 : int;

var ~alive4 : int;

var ~id2 : int;

var ~st4 : int;

var ~nomsg : int;

var ~st2 : int;

var ~mode1 : int;

var ~p2_new : int;

var ~mode3 : int;

var ~p2_old : int;

var ~p3_new : int;

var ~r1 : int;

var ~p1_old : int;

var ~alive1 : int;

var ~send3 : int;

var ~id3 : int;

var ~alive3 : int;

var ~send1 : int;

var ~st3 : int;

var ~id1 : int;

var ~st1 : int;

var ~mode2 : int;

var ~p4_old : int;

var ~mode4 : int;

var ~p1_new : int;

var ~p3_old : int;

procedure ULTIMATE.start() returns ()
modifies ~send4, ~alive2, ~send2, ~p4_new, ~id4, ~alive4, ~id2, ~st4, ~nomsg, ~st2, ~mode1, ~p2_new, ~mode3, ~p2_old, ~p3_new, ~r1, ~p1_old, ~alive1, ~send3, ~id3, ~alive3, ~send1, ~st3, ~id1, ~st1, ~mode2, ~p4_old, ~mode4, ~p1_new, ~p3_old;
{
    var assert_#in~arg : int;
    var main_#t~nondet10 : int;
    var main_#t~nondet11 : int;
    var main_~c1~108 : int;
    var main_#t~nondet12 : int;
    var main_#t~nondet13 : int;
    var main_#t~nondet14 : int;
    var init_~tmp~51 : int;
    var assert_~arg : int;
    var main_#t~nondet8 : int;
    var init_#res : int;
    var main_#t~nondet9 : int;
    var main_~i2~108 : int;
    var node1_#t~ite0 : int;
    var node1_#t~ite1 : int;
    var main_#t~ret29 : int;
    var node3_#t~ite4 : int;
    var node3_#t~ite5 : int;
    var main_#t~nondet27 : int;
    var main_#t~nondet26 : int;
    var main_#t~nondet28 : int;
    var main_#t~nondet21 : int;
    var main_#t~post31 : int;
    var main_#t~nondet20 : int;
    var main_#t~nondet23 : int;
    var check_#res : int;
    var main_#t~nondet22 : int;
    var main_#t~nondet25 : int;
    var main_#t~nondet24 : int;
    var node2_~m2~18 : int;
    var node4_#t~ite7 : int;
    var check_~tmp~101 : int;
    var node2_#t~ite3 : int;
    var main_#res : int;
    var node2_#t~ite2 : int;
    var node3_~m3~29 : int;
    var node4_#t~ite6 : int;
    var main_#t~nondet15 : int;
    var main_#t~nondet16 : int;
    var main_#t~ret30 : int;
    var node4_~m4~40 : int;
    var main_#t~nondet17 : int;
    var main_#t~nondet18 : int;
    var main_#t~nondet19 : int;
    var node1_~m1~7 : int;

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
    ~p4_old := 0;
    ~p4_new := 0;
    ~id4 := 0;
    ~st4 := 0;
    ~mode4 := 0;
    ~alive4 := 0;
    ~nomsg := -1;
    ~send1 := 0;
    ~send2 := 0;
    ~send3 := 0;
    ~send4 := 0;
    havoc main_#res;
    havoc main_#t~nondet10, main_#t~nondet11, main_~c1~108, main_#t~nondet12, main_#t~nondet13, main_#t~nondet14, main_#t~nondet8, main_#t~nondet9, main_~i2~108, main_#t~ret29, main_#t~nondet27, main_#t~nondet26, main_#t~nondet28, main_#t~nondet21, main_#t~post31, main_#t~nondet20, main_#t~nondet23, main_#t~nondet22, main_#t~nondet25, main_#t~nondet24, main_#t~nondet15, main_#t~nondet16, main_#t~ret30, main_#t~nondet17, main_#t~nondet18, main_#t~nondet19;
    havoc main_~c1~108;
    havoc main_~i2~108;
    main_~c1~108 := 0;
    assume main_#t~nondet8 <= 127 && 0 <= main_#t~nondet8 + 128;
    ~r1 := main_#t~nondet8;
    havoc main_#t~nondet8;
    assume main_#t~nondet9 <= 127 && 0 <= main_#t~nondet9 + 128;
    ~id1 := main_#t~nondet9;
    havoc main_#t~nondet9;
    assume 0 <= main_#t~nondet10 + 128 && main_#t~nondet10 <= 127;
    ~st1 := main_#t~nondet10;
    havoc main_#t~nondet10;
    assume 0 <= main_#t~nondet11 + 128 && main_#t~nondet11 <= 127;
    ~send1 := main_#t~nondet11;
    havoc main_#t~nondet11;
    ~mode1 := main_#t~nondet12;
    havoc main_#t~nondet12;
    ~alive1 := main_#t~nondet13;
    havoc main_#t~nondet13;
    assume main_#t~nondet14 <= 127 && 0 <= main_#t~nondet14 + 128;
    ~id2 := main_#t~nondet14;
    havoc main_#t~nondet14;
    assume main_#t~nondet15 <= 127 && 0 <= main_#t~nondet15 + 128;
    ~st2 := main_#t~nondet15;
    havoc main_#t~nondet15;
    assume main_#t~nondet16 <= 127 && 0 <= main_#t~nondet16 + 128;
    ~send2 := main_#t~nondet16;
    havoc main_#t~nondet16;
    ~mode2 := main_#t~nondet17;
    havoc main_#t~nondet17;
    ~alive2 := main_#t~nondet18;
    havoc main_#t~nondet18;
    assume main_#t~nondet19 <= 127 && 0 <= main_#t~nondet19 + 128;
    ~id3 := main_#t~nondet19;
    havoc main_#t~nondet19;
    assume 0 <= main_#t~nondet20 + 128 && main_#t~nondet20 <= 127;
    ~st3 := main_#t~nondet20;
    havoc main_#t~nondet20;
    assume main_#t~nondet21 <= 127 && 0 <= main_#t~nondet21 + 128;
    ~send3 := main_#t~nondet21;
    havoc main_#t~nondet21;
    ~mode3 := main_#t~nondet22;
    havoc main_#t~nondet22;
    ~alive3 := main_#t~nondet23;
    havoc main_#t~nondet23;
    assume 0 <= main_#t~nondet24 + 128 && main_#t~nondet24 <= 127;
    ~id4 := main_#t~nondet24;
    havoc main_#t~nondet24;
    assume 0 <= main_#t~nondet25 + 128 && main_#t~nondet25 <= 127;
    ~st4 := main_#t~nondet25;
    havoc main_#t~nondet25;
    assume 0 <= main_#t~nondet26 + 128 && main_#t~nondet26 <= 127;
    ~send4 := main_#t~nondet26;
    havoc main_#t~nondet26;
    ~mode4 := main_#t~nondet27;
    havoc main_#t~nondet27;
    ~alive4 := main_#t~nondet28;
    havoc main_#t~nondet28;
    havoc init_#res;
    havoc init_~tmp~51;
    havoc init_~tmp~51;
    assume ~r1 == 0;
    assume ((((1 <= ~alive3 + ~alive4 % 256 + ~alive1 % 256 + ~alive2 % 256 && ~alive2 < -256) && 0 <= ~alive3) && ~alive1 < -256) && 256 + 256 <= ~alive4) && ~alive3 < 256;
    assume 0 <= ~id1;
    assume ~st1 == 0;
    assume ~send1 == ~id1;
    assume ~mode1 + 256 == 0;
    assume 0 <= ~id2;
    assume ~st2 == 0;
    assume ~send2 == ~id2;
    assume ~mode2 % 256 == 0 && 256 + 256 <= ~mode2;
    assume 0 <= ~id3;
    assume ~st3 == 0;
    assume ~send3 == ~id3;
    assume ~mode3 < -256 && ~mode3 % 256 == 0;
    assume 0 <= ~id4;
    assume ~st4 == 0;
    assume ~send4 == ~id4;
    assume ~mode4 + 256 == 0;
    assume !(~id1 == ~id2);
    assume !(~id1 == ~id3);
    assume !(~id1 == ~id4);
    assume !(~id2 == ~id3);
    assume !(~id2 == ~id4);
    assume !(~id3 == ~id4);
    init_~tmp~51 := 1;
    init_#res := init_~tmp~51;
    main_#t~ret29 := init_#res;
    assume main_#t~ret29 <= 2147483647 && 0 <= main_#t~ret29 + 2147483648;
    main_~i2~108 := main_#t~ret29;
    havoc main_#t~ret29;
    assume !(main_~i2~108 == 0);
    ~p1_old := ~nomsg;
    ~p1_new := ~nomsg;
    ~p2_old := ~nomsg;
    ~p2_new := ~nomsg;
    ~p3_old := ~nomsg;
    ~p3_new := ~nomsg;
    ~p4_old := ~nomsg;
    ~p4_new := ~nomsg;
    main_~i2~108 := 0;
    goto loc1;
  loc1:
    assume main_~i2~108 < 8;
    havoc node1_#t~ite0, node1_#t~ite1, node1_~m1~7;
    havoc node1_~m1~7;
    node1_~m1~7 := ~nomsg;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume (~mode1 < 256 && !(~mode1 == 0)) && 0 <= ~mode1;
    assume (~r1 <= 126 && 0 <= ~r1 + 1) && ~r1 + 1 < 256;
    ~r1 := ~r1 + 1;
    node1_~m1~7 := ~p4_old;
    ~p4_old := ~nomsg;
    assume node1_~m1~7 == ~nomsg;
    ~mode1 := 0;
    goto loc3;
  loc2_1:
    assume ~mode1 + 256 == 0;
    assume ~alive1 < -256 && ~alive1 % 256 == 0;
    assume ~send1 == ~id1;
    ~mode1 := 1;
    goto loc3;
  loc3:
    havoc node2_#t~ite3, node2_#t~ite2, node2_~m2~18;
    havoc node2_~m2~18;
    node2_~m2~18 := ~nomsg;
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume 256 + 256 <= ~mode2 && ~mode2 % 256 == 0;
    assume ~alive2 % 256 == 0 && ~alive2 < -256;
    assume ~send2 == ~id2;
    ~mode2 := 1;
    goto loc5;
  loc4_1:
    assume (0 <= ~mode2 && ~mode2 < 256) && !(~mode2 == 0);
    node2_~m2~18 := ~p1_old;
    ~p1_old := ~nomsg;
    assume node2_~m2~18 == ~nomsg;
    ~mode2 := 0;
    goto loc5;
  loc5:
    havoc node3_#t~ite4, node3_#t~ite5, node3_~m3~29;
    havoc node3_~m3~29;
    node3_~m3~29 := ~nomsg;
    goto loc6;
  loc6:
    goto loc6_0, loc6_1;
  loc6_0:
    assume (!(~mode3 == 0) && 0 <= ~mode3) && ~mode3 < 256;
    node3_~m3~29 := ~p2_old;
    ~p2_old := ~nomsg;
    assume node3_~m3~29 == ~nomsg;
    ~mode3 := 0;
    goto loc7;
  loc6_1:
    assume ~mode3 < -256 && ~mode3 % 256 == 0;
    assume (~alive3 < 256 && !(~alive3 == 0)) && 0 <= ~alive3;
    assume ~p3_new == ~nomsg && !(~send3 == ~nomsg);
    node3_#t~ite4 := ~send3;
    assume (node3_#t~ite4 <= 127 && 0 <= node3_#t~ite4) && node3_#t~ite4 < 256;
    ~p3_new := node3_#t~ite4;
    havoc node3_#t~ite4;
    ~mode3 := 1;
    goto loc7;
  loc7:
    havoc node4_#t~ite7, node4_#t~ite6, node4_~m4~40;
    havoc node4_~m4~40;
    node4_~m4~40 := ~nomsg;
    goto loc8;
  loc8:
    goto loc8_0, loc8_1;
  loc8_0:
    assume ~mode4 + 256 == 0;
    assume ~alive4 % 256 == 0 && 256 + 256 <= ~alive4;
    assume ~send4 == ~id4;
    ~mode4 := 1;
    goto loc9;
  loc8_1:
    assume (0 <= ~mode4 && !(~mode4 == 0)) && ~mode4 < 256;
    node4_~m4~40 := ~p3_old;
    ~p3_old := ~nomsg;
    assume node4_~m4~40 == ~nomsg;
    ~mode4 := 0;
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
    havoc check_~tmp~101;
    havoc check_~tmp~101;
    assume ~st2 + ~st1 + ~st4 + ~st3 <= 1;
    goto loc10;
  loc10:
    goto loc10_0, loc10_1;
  loc10_0:
    assume !(~r1 < 4);
    assume !(~st1 + ~st3 + ~st2 + ~st4 == 1);
    check_~tmp~101 := 0;
    goto loc11;
  loc10_1:
    assume ~r1 < 4;
    check_~tmp~101 := 1;
    goto loc11;
  loc11:
    check_#res := check_~tmp~101;
    main_#t~ret30 := check_#res;
    assume 0 <= main_#t~ret30 + 2147483648 && main_#t~ret30 <= 2147483647;
    main_~c1~108 := main_#t~ret30;
    havoc main_#t~ret30;
    goto loc12;
  loc12:
    goto loc12_0, loc12_1;
  loc12_0:
    assume !(main_~c1~108 == 0);
    assert_#in~arg := 1;
    goto loc13;
  loc12_1:
    assume main_~c1~108 == 0;
    assert_#in~arg := 0;
    goto loc13;
  loc13:
    havoc assert_~arg;
    assert_~arg := assert_#in~arg;
    goto loc14;
  loc14:
    goto loc14_0, loc14_1;
  loc14_0:
    assume (0 <= assert_~arg && !(assert_~arg == 0)) && assert_~arg < 256;
    main_#t~post31 := main_~i2~108;
    main_~i2~108 := main_#t~post31 + 1;
    havoc main_#t~post31;
    goto loc1;
  loc14_1:
    assume assert_~arg == 0;
    goto loc15;
  loc15:
    assert false;
}

