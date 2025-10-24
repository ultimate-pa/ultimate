procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_~k~0 : int;
    var main_#t~nondet1 : int;
    var __VERIFIER_assert_~cond : int;
    var main_#t~nondet2 : int;
    var main_#t~post3 : int;
    var main_~i1~0 : int;
    var main_#t~post7 : int;
    var main_#t~post6 : int;
    var main_#t~post5 : int;
    var main_~n1~0 : int;
    var main_#t~post4 : int;
    var main_#t~post8 : int;
    var main_#res : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~i0~0 : int;
    var main_~j1~0 : int;
    var main_~n0~0 : int;

  loc0:
    havoc main_#res;
    havoc main_~k~0, main_#t~nondet1, main_#t~nondet2, main_#t~post3, main_~i1~0, main_#t~post7, main_#t~post6, main_#t~post5, main_~n1~0, main_#t~post4, main_#t~post8, main_~i0~0, main_~j1~0, main_~n0~0;
    havoc main_~n0~0;
    havoc main_~n1~0;
    main_~i0~0 := 0;
    main_~k~0 := 0;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    main_~n0~0 := main_#t~nondet1;
    havoc main_#t~nondet1;
    assume 0 <= main_#t~nondet2 + 2147483648 && main_#t~nondet2 <= 2147483647;
    main_~n1~0 := main_#t~nondet2;
    havoc main_#t~nondet2;
    assume 0 <= main_~n0~0 + 1000000 && main_~n0~0 < 1000000;
    assume 0 <= main_~n1~0 + 1000000 && main_~n1~0 < 1000000;
    assume !(main_~i0~0 < main_~n0~0);
    main_~i1~0 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~i1~0 < main_~n1~0);
    main_~j1~0 := 0;
    goto loc3;
  loc2_1:
    assume main_~i1~0 < main_~n1~0;
    main_#t~post5 := main_~i1~0;
    main_~i1~0 := main_#t~post5 + 1;
    havoc main_#t~post5;
    main_#t~post6 := main_~k~0;
    main_~k~0 := main_#t~post6 + 1;
    havoc main_#t~post6;
    goto loc1;
  loc3:
    assume main_~j1~0 < main_~n0~0 + main_~n1~0;
    __VERIFIER_assert_#in~cond := (if 0 < main_~k~0 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume 0 == __VERIFIER_assert_~cond;
    goto loc5;
  loc4_1:
    assume !(0 == __VERIFIER_assert_~cond);
    main_#t~post7 := main_~j1~0;
    main_~j1~0 := main_#t~post7 + 1;
    havoc main_#t~post7;
    main_#t~post8 := main_~k~0;
    main_~k~0 := main_#t~post8 + -1;
    havoc main_#t~post8;
    goto loc3;
  loc5:
    assert false;
}

