procedure ULTIMATE.start() returns ()
modifies ;
{
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_#t~post0 : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~i~4 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~post0, main_~i~4;
    havoc main_~i~4;
    main_~i~4 := 0;
    goto loc1;
  loc1:
    assume !(main_~i~4 == 1000000);
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume main_~i~4 <= 1000000;
    __VERIFIER_assert_#in~cond := 1;
    goto loc3;
  loc2_1:
    assume !(main_~i~4 <= 1000000);
    __VERIFIER_assert_#in~cond := 0;
    goto loc3;
  loc3:
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume !(__VERIFIER_assert_~cond == 0);
    main_#t~post0 := main_~i~4;
    main_~i~4 := main_#t~post0 + 1;
    havoc main_#t~post0;
    goto loc1;
  loc4_1:
    assume __VERIFIER_assert_~cond == 0;
    goto loc5;
  loc5:
    assert false;
}

