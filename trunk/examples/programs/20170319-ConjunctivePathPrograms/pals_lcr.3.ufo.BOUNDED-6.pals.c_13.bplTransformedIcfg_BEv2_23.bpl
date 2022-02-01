var ~p1_old : int;

var ~send2 : int;

var ~send3 : int;

var ~id3 : int;

var ~send1 : int;

var ~id2 : int;

var ~st3 : int;

var ~id1 : int;

var ~st1 : int;

var ~nomsg : int;

var ~st2 : int;

var ~mode2 : int;

var ~mode1 : int;

var ~p2_new : int;

var ~mode3 : int;

var ~p2_old : int;

var ~p1_new : int;

var ~p3_old : int;

var ~p3_new : int;

var ~r1 : int;

procedure ULTIMATE.start() returns ()
modifies ~p1_old, ~send2, ~send3, ~id3, ~send1, ~id2, ~st3, ~id1, ~st1, ~nomsg, ~st2, ~mode2, ~mode1, ~p2_new, ~mode3, ~p2_old, ~p1_new, ~p3_old, ~p3_new, ~r1;
{
    var assert_#in~arg : int;
    var main_#t~nondet10 : int;
    var main_#t~nondet4 : int;
    var main_#t~nondet11 : int;
    var main_#t~nondet5 : int;
    var main_#t~nondet12 : int;
    var main_#t~nondet13 : int;
    var main_#t~nondet3 : int;
    var main_#t~nondet14 : int;
    var assert_~arg : int;
    var main_#t~nondet8 : int;
    var init_#res : int;
    var main_#t~nondet9 : int;
    var main_#t~nondet6 : int;
    var main_#t~nondet7 : int;
    var node1_#t~ite0 : int;
    var node2_~m2~14 : int;
    var node3_#t~ite2 : int;
    var check_#res : int;
    var check_~tmp~62 : int;
    var main_#t~post18 : int;
    var init_~tmp~28 : int;
    var main_#t~ret16 : int;
    var main_#t~ret17 : int;
    var main_~i2~72 : int;
    var main_#res : int;
    var node2_#t~ite1 : int;
    var main_#t~nondet15 : int;
    var node1_~m1~7 : int;
    var main_~c1~72 : int;
    var node3_~m3~21 : int;

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
    ~nomsg := -1;
    ~send1 := 0;
    ~send2 := 0;
    ~send3 := 0;
    havoc main_#res;
    havoc main_#t~nondet10, main_#t~nondet4, main_#t~nondet11, main_#t~nondet5, main_#t~nondet12, main_#t~nondet13, main_#t~nondet3, main_#t~nondet14, main_#t~nondet8, main_#t~nondet9, main_#t~nondet6, main_#t~nondet7, main_#t~post18, main_#t~ret16, main_#t~ret17, main_~i2~72, main_#t~nondet15, main_~c1~72;
    havoc main_~c1~72;
    havoc main_~i2~72;
    main_~c1~72 := 0;
    assume 0 <= main_#t~nondet3 + 128 && main_#t~nondet3 <= 127;
    ~r1 := main_#t~nondet3;
    havoc main_#t~nondet3;
    assume main_#t~nondet4 <= 127 && 0 <= main_#t~nondet4 + 128;
    ~id1 := main_#t~nondet4;
    havoc main_#t~nondet4;
    assume main_#t~nondet5 <= 127 && 0 <= main_#t~nondet5 + 128;
    ~st1 := main_#t~nondet5;
    havoc main_#t~nondet5;
    assume main_#t~nondet6 <= 127 && 0 <= main_#t~nondet6 + 128;
    ~send1 := main_#t~nondet6;
    havoc main_#t~nondet6;
    ~mode1 := main_#t~nondet7;
    havoc main_#t~nondet7;
    assume main_#t~nondet8 <= 127 && 0 <= main_#t~nondet8 + 128;
    ~id2 := main_#t~nondet8;
    havoc main_#t~nondet8;
    assume main_#t~nondet9 <= 127 && 0 <= main_#t~nondet9 + 128;
    ~st2 := main_#t~nondet9;
    havoc main_#t~nondet9;
    assume 0 <= main_#t~nondet10 + 128 && main_#t~nondet10 <= 127;
    ~send2 := main_#t~nondet10;
    havoc main_#t~nondet10;
    ~mode2 := main_#t~nondet11;
    havoc main_#t~nondet11;
    assume 0 <= main_#t~nondet12 + 128 && main_#t~nondet12 <= 127;
    ~id3 := main_#t~nondet12;
    havoc main_#t~nondet12;
    assume main_#t~nondet13 <= 127 && 0 <= main_#t~nondet13 + 128;
    ~st3 := main_#t~nondet13;
    havoc main_#t~nondet13;
    assume main_#t~nondet14 <= 127 && 0 <= main_#t~nondet14 + 128;
    ~send3 := main_#t~nondet14;
    havoc main_#t~nondet14;
    ~mode3 := main_#t~nondet15;
    havoc main_#t~nondet15;
    havoc init_#res;
    havoc init_~tmp~28;
    havoc init_~tmp~28;
    assume ~r1 == 0;
    assume 0 <= ~id1;
    assume ~st1 == 0;
    assume ~send1 == ~id1;
    assume ~mode1 - 256 == 0;
    assume 0 <= ~id2;
    assume ~st2 == 0;
    assume ~send2 == ~id2;
    assume ~mode2 % 256 == 0 && 256 + 256 <= ~mode2;
    assume 0 <= ~id3;
    assume ~st3 == 0;
    assume ~send3 == ~id3;
    assume ~mode3 == 0;
    assume !(~id1 == ~id2);
    assume !(~id1 == ~id3);
    assume !(~id2 == ~id3);
    init_~tmp~28 := 1;
    init_#res := init_~tmp~28;
    main_#t~ret16 := init_#res;
    assume 0 <= main_#t~ret16 + 2147483648 && main_#t~ret16 <= 2147483647;
    main_~i2~72 := main_#t~ret16;
    havoc main_#t~ret16;
    assume !(main_~i2~72 == 0);
    ~p1_old := ~nomsg;
    ~p1_new := ~nomsg;
    ~p2_old := ~nomsg;
    ~p2_new := ~nomsg;
    ~p3_old := ~nomsg;
    ~p3_new := ~nomsg;
    main_~i2~72 := 0;
    goto loc1;
  loc1:
    assume main_~i2~72 < 6;
    havoc node1_#t~ite0, node1_~m1~7;
    havoc node1_~m1~7;
    node1_~m1~7 := ~nomsg;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume ~mode1 - 256 == 0;
    assume ~p1_new == ~nomsg && !(~send1 == ~nomsg);
    node1_#t~ite0 := ~send1;
    assume (node1_#t~ite0 <= 127 && node1_#t~ite0 < 256) && 0 <= node1_#t~ite0;
    ~p1_new := node1_#t~ite0;
    havoc node1_#t~ite0;
    ~mode1 := 1;
    goto loc3;
  loc2_1:
    assume (!(~mode1 == 0) && ~mode1 < 256) && 0 <= ~mode1;
    assume (~r1 <= 126 && 0 <= ~r1 + 1) && ~r1 + 1 < 256;
    ~r1 := ~r1 + 1;
    node1_~m1~7 := ~p3_old;
    ~p3_old := ~nomsg;
    assume node1_~m1~7 == ~nomsg;
    ~mode1 := 0;
    goto loc3;
  loc3:
    havoc node2_~m2~14, node2_#t~ite1;
    havoc node2_~m2~14;
    node2_~m2~14 := ~nomsg;
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume (0 <= ~mode2 && ~mode2 < 256) && !(~mode2 == 0);
    node2_~m2~14 := ~p1_old;
    ~p1_old := ~nomsg;
    assume node2_~m2~14 == ~nomsg;
    ~mode2 := 0;
    goto loc5;
  loc4_1:
    assume 256 + 256 <= ~mode2 && ~mode2 % 256 == 0;
    assume ~p2_new == ~nomsg && !(~send2 == ~nomsg);
    node2_#t~ite1 := ~send2;
    assume (node2_#t~ite1 < 256 && 0 <= node2_#t~ite1) && node2_#t~ite1 <= 127;
    ~p2_new := node2_#t~ite1;
    havoc node2_#t~ite1;
    ~mode2 := 1;
    goto loc5;
  loc5:
    havoc node3_#t~ite2, node3_~m3~21;
    havoc node3_~m3~21;
    node3_~m3~21 := ~nomsg;
    goto loc6;
  loc6:
    goto loc6_0, loc6_1;
  loc6_0:
    assume (!(~mode3 == 0) && 0 <= ~mode3) && ~mode3 < 256;
    node3_~m3~21 := ~p2_old;
    ~p2_old := ~nomsg;
    assume node3_~m3~21 == ~nomsg;
    ~mode3 := 0;
    goto loc7;
  loc6_1:
    assume ~mode3 == 0;
    assume ~p3_new == ~nomsg && !(~send3 == ~nomsg);
    node3_#t~ite2 := ~send3;
    assume (node3_#t~ite2 < 256 && 0 <= node3_#t~ite2) && node3_#t~ite2 <= 127;
    ~p3_new := node3_#t~ite2;
    havoc node3_#t~ite2;
    ~mode3 := 1;
    goto loc7;
  loc7:
    ~p1_old := ~p1_new;
    ~p1_new := ~nomsg;
    ~p2_old := ~p2_new;
    ~p2_new := ~nomsg;
    ~p3_old := ~p3_new;
    ~p3_new := ~nomsg;
    havoc check_#res;
    havoc check_~tmp~62;
    havoc check_~tmp~62;
    assume ~st2 + ~st1 + ~st3 <= 1;
    goto loc8;
  loc8:
    goto loc8_0, loc8_1;
  loc8_0:
    assume !(3 <= ~r1);
    assume ~st1 + ~st3 + ~st2 == 0;
    goto loc9;
  loc8_1:
    assume 3 <= ~r1;
    goto loc9;
  loc9:
    goto loc9_0, loc9_1;
  loc9_0:
    assume ~r1 < 3;
    check_~tmp~62 := 1;
    goto loc10;
  loc9_1:
    assume !(~r1 < 3);
    assume !(~st2 + ~st1 + ~st3 == 1);
    check_~tmp~62 := 0;
    goto loc10;
  loc10:
    check_#res := check_~tmp~62;
    main_#t~ret17 := check_#res;
    assume main_#t~ret17 <= 2147483647 && 0 <= main_#t~ret17 + 2147483648;
    main_~c1~72 := main_#t~ret17;
    havoc main_#t~ret17;
    goto loc11;
  loc11:
    goto loc11_0, loc11_1;
  loc11_0:
    assume !(main_~c1~72 == 0);
    assert_#in~arg := 1;
    goto loc12;
  loc11_1:
    assume main_~c1~72 == 0;
    assert_#in~arg := 0;
    goto loc12;
  loc12:
    havoc assert_~arg;
    assert_~arg := assert_#in~arg;
    goto loc13;
  loc13:
    goto loc13_0, loc13_1;
  loc13_0:
    assume (0 <= assert_~arg && !(assert_~arg == 0)) && assert_~arg < 256;
    main_#t~post18 := main_~i2~72;
    main_~i2~72 := main_#t~post18 + 1;
    havoc main_#t~post18;
    goto loc1;
  loc13_1:
    assume assert_~arg == 0;
    goto loc14;
  loc14:
    assert false;
}

