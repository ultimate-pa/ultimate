procedure ULTIMATE.start() returns ()
modifies ;
{
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_~x~4 : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~y~4 : int;

  loc0:
    havoc main_#res;
    havoc main_~x~4, main_~y~4;
    main_~x~4 := 0;
    main_~y~4 := 50;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume main_~x~4 < 100;
    goto loc3;
  loc2_1:
    assume !(main_~x~4 < 100);
    assume !(main_~y~4 == 100);
    __VERIFIER_assert_#in~cond := 0;
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    goto loc4;
  loc3:
    goto loc3_0, loc3_1;
  loc3_0:
    assume main_~x~4 < 50;
    main_~x~4 := main_~x~4 + 1;
    goto loc1;
  loc3_1:
    assume !(main_~x~4 < 50);
    main_~x~4 := main_~x~4 + 1;
    main_~y~4 := main_~y~4 + 1;
    goto loc1;
  loc4:
    assert false;
}

