implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~nondet0 : int;
    var main_#t~post1 : int;
    var main_~x~5 : int;
    var main_~y~5 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet0, main_#t~post1, main_~x~5, main_~y~5;
    main_~x~5 := 0;
    main_~y~5 := main_#t~nondet0;
    havoc main_#t~nondet0;
    goto loc1;
  loc1:
    assume true;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~x~5 % 4294967296 < 99);
    __VERIFIER_assert_#in~cond := (if (if main_~x~5 % 4294967296 < 0 && main_~x~5 % 4294967296 % 2 != 0 then main_~x~5 % 4294967296 % 2 - 2 else main_~x~5 % 4294967296 % 2) % 4294967296 == (if main_~y~5 % 4294967296 < 0 && main_~y~5 % 4294967296 % 2 != 0 then main_~y~5 % 4294967296 % 2 - 2 else main_~y~5 % 4294967296 % 2) % 4294967296 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc3;
  loc2_1:
    assume !!(main_~x~5 % 4294967296 < 99);
    assume (if main_~y~5 % 4294967296 < 0 && main_~y~5 % 4294967296 % 2 != 0 then main_~y~5 % 4294967296 % 2 - 2 else main_~y~5 % 4294967296 % 2) % 4294967296 == 0;
    main_#t~post1 := main_~x~5;
    main_~x~5 := main_#t~post1 + 1;
    havoc main_#t~post1;
    assume (if main_~y~5 % 4294967296 < 0 && main_~y~5 % 4294967296 % 2 != 0 then main_~y~5 % 4294967296 % 2 - 2 else main_~y~5 % 4294967296 % 2) % 4294967296 == 0;
    main_~x~5 := main_~x~5 + 2;
    assume (if main_~y~5 % 4294967296 < 0 && main_~y~5 % 4294967296 % 2 != 0 then main_~y~5 % 4294967296 % 2 - 2 else main_~y~5 % 4294967296 % 2) % 4294967296 == 0;
    main_~x~5 := main_~x~5 + 2;
    assume (if main_~y~5 % 4294967296 < 0 && main_~y~5 % 4294967296 % 2 != 0 then main_~y~5 % 4294967296 % 2 - 2 else main_~y~5 % 4294967296 % 2) % 4294967296 == 0;
    main_~x~5 := main_~x~5 + 2;
    assume (if main_~y~5 % 4294967296 < 0 && main_~y~5 % 4294967296 % 2 != 0 then main_~y~5 % 4294967296 % 2 - 2 else main_~y~5 % 4294967296 % 2) % 4294967296 == 0;
    main_~x~5 := main_~x~5 + 2;
    assume (if main_~y~5 % 4294967296 < 0 && main_~y~5 % 4294967296 % 2 != 0 then main_~y~5 % 4294967296 % 2 - 2 else main_~y~5 % 4294967296 % 2) % 4294967296 == 0;
    main_~x~5 := main_~x~5 + 2;
    assume (if main_~y~5 % 4294967296 < 0 && main_~y~5 % 4294967296 % 2 != 0 then main_~y~5 % 4294967296 % 2 - 2 else main_~y~5 % 4294967296 % 2) % 4294967296 == 0;
    main_~x~5 := main_~x~5 + 2;
    assume (if main_~y~5 % 4294967296 < 0 && main_~y~5 % 4294967296 % 2 != 0 then main_~y~5 % 4294967296 % 2 - 2 else main_~y~5 % 4294967296 % 2) % 4294967296 == 0;
    main_~x~5 := main_~x~5 + 2;
    assume (if main_~y~5 % 4294967296 < 0 && main_~y~5 % 4294967296 % 2 != 0 then main_~y~5 % 4294967296 % 2 - 2 else main_~y~5 % 4294967296 % 2) % 4294967296 == 0;
    main_~x~5 := main_~x~5 + 2;
    assume (if main_~y~5 % 4294967296 < 0 && main_~y~5 % 4294967296 % 2 != 0 then main_~y~5 % 4294967296 % 2 - 2 else main_~y~5 % 4294967296 % 2) % 4294967296 == 0;
    main_~x~5 := main_~x~5 + 2;
    goto loc1;
  loc3:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

