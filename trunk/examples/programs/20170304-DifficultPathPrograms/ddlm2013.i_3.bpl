implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~nondet0 : int;
    var main_#t~post2 : int;
    var main_#t~post3 : int;
    var main_#t~nondet1 : int;
    var main_~i~5 : int;
    var main_~j~5 : int;
    var main_~a~5 : int;
    var main_~b~5 : int;
    var main_~flag~5 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet0, main_#t~post2, main_#t~post3, main_#t~nondet1, main_~i~5, main_~j~5, main_~a~5, main_~b~5, main_~flag~5;
    havoc main_~i~5;
    havoc main_~j~5;
    havoc main_~a~5;
    havoc main_~b~5;
    assume -2147483648 <= main_#t~nondet0 && main_#t~nondet0 <= 2147483647;
    main_~flag~5 := main_#t~nondet0;
    havoc main_#t~nondet0;
    main_~a~5 := 0;
    main_~b~5 := 0;
    main_~j~5 := 1;
    assume main_~flag~5 != 0;
    main_~i~5 := 0;
    goto loc1;
  loc1:
    assume true;
    assume -2147483648 <= main_#t~nondet1 && main_#t~nondet1 <= 2147483647;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !!(main_#t~nondet1 != 0);
    havoc main_#t~nondet1;
    main_#t~post2 := main_~a~5;
    main_~a~5 := main_#t~post2 + 1;
    havoc main_#t~post2;
    main_~b~5 := main_~b~5 + (main_~j~5 - main_~i~5);
    main_~i~5 := main_~i~5 + 2;
    assume (if main_~i~5 % 4294967296 < 0 && main_~i~5 % 4294967296 % 2 != 0 then main_~i~5 % 4294967296 % 2 - 2 else main_~i~5 % 4294967296 % 2) % 4294967296 == 0;
    main_~j~5 := main_~j~5 + 2;
    goto loc1;
  loc2_1:
    assume !(main_#t~nondet1 != 0);
    havoc main_#t~nondet1;
    assume main_~flag~5 != 0;
    __VERIFIER_assert_#in~cond := (if main_~a~5 % 4294967296 == main_~b~5 % 4294967296 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc3;
  loc3:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

