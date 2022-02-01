implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~nondet0 : int;
    var main_#t~nondet1 : int;
    var main_~a~5 : int;
    var main_~b~5 : int;
    var main_~res~5 : int;
    var main_~cnt~5 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet0, main_#t~nondet1, main_~a~5, main_~b~5, main_~res~5, main_~cnt~5;
    assume -2147483648 <= main_#t~nondet0 && main_#t~nondet0 <= 2147483647;
    main_~a~5 := main_#t~nondet0;
    havoc main_#t~nondet0;
    assume -2147483648 <= main_#t~nondet1 && main_#t~nondet1 <= 2147483647;
    main_~b~5 := main_#t~nondet1;
    havoc main_#t~nondet1;
    havoc main_~res~5;
    havoc main_~cnt~5;
    assume !!(main_~a~5 <= 1000000);
    assume !!(0 <= main_~b~5 && main_~b~5 <= 1000000);
    main_~res~5 := main_~a~5;
    main_~cnt~5 := main_~b~5;
    goto loc1;
  loc1:
    assume true;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~cnt~5 > 0);
    __VERIFIER_assert_#in~cond := (if main_~res~5 == main_~a~5 + main_~b~5 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc3;
  loc2_1:
    assume !!(main_~cnt~5 > 0);
    main_~cnt~5 := main_~cnt~5 - 1;
    main_~res~5 := main_~res~5 + 1;
    goto loc1;
  loc3:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

