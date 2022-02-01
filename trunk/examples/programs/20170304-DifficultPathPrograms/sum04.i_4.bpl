implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~post0 : int;
    var main_~i~4 : int;
    var main_~sn~4 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    havoc main_#res;
    havoc main_#t~post0, main_~i~4, main_~sn~4;
    havoc main_~i~4;
    main_~sn~4 := 0;
    main_~i~4 := 1;
    goto loc1;
  loc1:
    assume true;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~i~4 <= 8);
    __VERIFIER_assert_#in~cond := (if main_~sn~4 == 16 || main_~sn~4 == 0 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc3;
  loc2_1:
    assume !!(main_~i~4 <= 8);
    goto loc4;
  loc3:
    assert false;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume main_~i~4 < 4;
    main_~sn~4 := main_~sn~4 + 2;
    goto loc5;
  loc4_1:
    assume !(main_~i~4 < 4);
    goto loc5;
  loc5:
    main_#t~post0 := main_~i~4;
    main_~i~4 := main_#t~post0 + 1;
    havoc main_#t~post0;
    goto loc1;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

