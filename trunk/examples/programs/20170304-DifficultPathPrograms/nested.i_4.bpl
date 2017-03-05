implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~nondet0 : int;
    var main_#t~nondet1 : int;
    var main_#t~post4 : int;
    var main_#t~post3 : int;
    var main_#t~post2 : int;
    var main_~n~5 : int;
    var main_~m~5 : int;
    var main_~k~5 : int;
    var main_~i~5 : int;
    var main_~j~5 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet0, main_#t~nondet1, main_#t~post4, main_#t~post3, main_#t~post2, main_~n~5, main_~m~5, main_~k~5, main_~i~5, main_~j~5;
    assume -2147483648 <= main_#t~nondet0 && main_#t~nondet0 <= 2147483647;
    main_~n~5 := main_#t~nondet0;
    havoc main_#t~nondet0;
    assume -2147483648 <= main_#t~nondet1 && main_#t~nondet1 <= 2147483647;
    main_~m~5 := main_#t~nondet1;
    havoc main_#t~nondet1;
    main_~k~5 := 0;
    havoc main_~i~5;
    havoc main_~j~5;
    assume !!(10 <= main_~n~5 && main_~n~5 <= 10000);
    assume !!(10 <= main_~m~5 && main_~m~5 <= 10000);
    main_~i~5 := 0;
    goto loc1;
  loc1:
    assume true;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~i~5 < main_~n~5);
    __VERIFIER_assert_#in~cond := (if main_~k~5 >= 100 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc3;
  loc2_1:
    assume !!(main_~i~5 < main_~n~5);
    main_~j~5 := 0;
    goto loc4;
  loc3:
    assert false;
  loc4:
    assume true;
    goto loc5;
  loc5:
    goto loc5_0, loc5_1;
  loc5_0:
    assume !(main_~j~5 < main_~m~5);
    main_#t~post2 := main_~i~5;
    main_~i~5 := main_#t~post2 + 1;
    havoc main_#t~post2;
    goto loc1;
  loc5_1:
    assume !!(main_~j~5 < main_~m~5);
    main_#t~post4 := main_~k~5;
    main_~k~5 := main_#t~post4 + 1;
    havoc main_#t~post4;
    main_#t~post3 := main_~j~5;
    main_~j~5 := main_#t~post3 + 1;
    havoc main_#t~post3;
    goto loc4;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

