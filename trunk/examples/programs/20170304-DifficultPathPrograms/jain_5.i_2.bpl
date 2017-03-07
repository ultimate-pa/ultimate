implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_~x~4 : int;
    var main_~y~4 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    havoc main_#res;
    havoc main_~x~4, main_~y~4;
    havoc main_~x~4;
    havoc main_~y~4;
    main_~x~4 := 0;
    main_~y~4 := 4;
    goto loc1;
  loc1:
    assume true;
    assume !false;
    main_~x~4 := main_~x~4 + main_~y~4;
    main_~y~4 := main_~y~4 + 4;
    __VERIFIER_assert_#in~cond := (if main_~x~4 % 4294967296 != 30 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(__VERIFIER_assert_~cond == 0);
    goto loc1;
  loc2_1:
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc3;
  loc3:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

