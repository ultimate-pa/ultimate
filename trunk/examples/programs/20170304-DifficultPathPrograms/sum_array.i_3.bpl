implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~nondet0 : int;
    var main_#t~nondet2 : int;
    var main_#t~post1 : int;
    var main_#t~nondet4 : int;
    var main_#t~post3 : int;
    var main_#t~post5 : int;
    var main_#t~post6 : int;
    var main_~M~6 : int;
    var main_~A~6 : [int]int;
    var main_~B~6 : [int]int;
    var main_~C~6 : [int]int;
    var main_~i~6 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet0, main_#t~nondet2, main_#t~post1, main_#t~nondet4, main_#t~post3, main_#t~post5, main_#t~post6, main_~M~6, main_~A~6, main_~B~6, main_~C~6, main_~i~6;
    main_~M~6 := main_#t~nondet0;
    havoc main_#t~nondet0;
    havoc main_~A~6;
    havoc main_~B~6;
    havoc main_~C~6;
    havoc main_~i~6;
    main_~i~6 := 0;
    goto loc1;
  loc1:
    assume true;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~i~6 % 4294967296 < main_~M~6 % 4294967296);
    main_~i~6 := 0;
    goto loc3;
  loc2_1:
    assume !!(main_~i~6 % 4294967296 < main_~M~6 % 4294967296);
    assume -2147483648 <= main_#t~nondet2 && main_#t~nondet2 <= 2147483647;
    main_~A~6 := main_~A~6[main_~i~6 % 4294967296 := main_#t~nondet2];
    havoc main_#t~nondet2;
    assume !!(main_~A~6[main_~i~6 % 4294967296] <= 1000000);
    main_#t~post1 := main_~i~6;
    main_~i~6 := main_#t~post1 + 1;
    havoc main_#t~post1;
    goto loc1;
  loc3:
    assume true;
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume !(main_~i~6 % 4294967296 < main_~M~6 % 4294967296);
    main_~i~6 := 0;
    goto loc5;
  loc4_1:
    assume !!(main_~i~6 % 4294967296 < main_~M~6 % 4294967296);
    assume -2147483648 <= main_#t~nondet4 && main_#t~nondet4 <= 2147483647;
    main_~B~6 := main_~B~6[main_~i~6 % 4294967296 := main_#t~nondet4];
    havoc main_#t~nondet4;
    assume !!(main_~B~6[main_~i~6 % 4294967296] <= 1000000);
    main_#t~post3 := main_~i~6;
    main_~i~6 := main_#t~post3 + 1;
    havoc main_#t~post3;
    goto loc3;
  loc5:
    assume true;
    goto loc6;
  loc6:
    goto loc6_0, loc6_1;
  loc6_0:
    assume !(main_~i~6 % 4294967296 < main_~M~6 % 4294967296);
    main_~i~6 := 0;
    assume true;
    assume !!(main_~i~6 % 4294967296 < main_~M~6 % 4294967296);
    __VERIFIER_assert_#in~cond := (if main_~C~6[main_~i~6 % 4294967296] == main_~A~6[main_~i~6 % 4294967296] + main_~B~6[main_~i~6 % 4294967296] then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc7;
  loc6_1:
    assume !!(main_~i~6 % 4294967296 < main_~M~6 % 4294967296);
    main_~C~6 := main_~C~6[main_~i~6 % 4294967296 := main_~A~6[main_~i~6 % 4294967296] + main_~B~6[main_~i~6 % 4294967296]];
    main_#t~post5 := main_~i~6;
    main_~i~6 := main_#t~post5 + 1;
    havoc main_#t~post5;
    goto loc5;
  loc7:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

