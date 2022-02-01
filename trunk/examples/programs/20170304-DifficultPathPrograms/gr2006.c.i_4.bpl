implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~post0 : int;
    var main_#t~post1 : int;
    var main_#t~post2 : int;
    var main_~x~4 : int;
    var main_~y~4 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    havoc main_#res;
    havoc main_#t~post0, main_#t~post1, main_#t~post2, main_~x~4, main_~y~4;
    havoc main_~x~4;
    havoc main_~y~4;
    main_~x~4 := 0;
    main_~y~4 := 0;
    goto loc1;
  loc1:
    assume true;
    assume !false;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume main_~x~4 < 50;
    main_#t~post0 := main_~y~4;
    main_~y~4 := main_#t~post0 + 1;
    havoc main_#t~post0;
    goto loc3;
  loc2_1:
    assume !(main_~x~4 < 50);
    main_#t~post1 := main_~y~4;
    main_~y~4 := main_#t~post1 - 1;
    havoc main_#t~post1;
    goto loc3;
  loc3:
    goto loc3_0, loc3_1;
  loc3_0:
    assume main_~y~4 < 0;
    __VERIFIER_assert_#in~cond := (if main_~x~4 == 100 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc4;
  loc3_1:
    assume !(main_~y~4 < 0);
    main_#t~post2 := main_~x~4;
    main_~x~4 := main_#t~post2 + 1;
    havoc main_#t~post2;
    goto loc1;
  loc4:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

