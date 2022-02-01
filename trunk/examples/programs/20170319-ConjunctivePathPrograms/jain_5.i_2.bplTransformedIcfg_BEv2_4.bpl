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
    havoc main_~x~4;
    havoc main_~y~4;
    main_~x~4 := 0;
    main_~y~4 := 4;
    goto loc1;
  loc1:
    main_~x~4 := main_~x~4 + main_~y~4;
    main_~y~4 := main_~y~4 + 4;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume (-4294967296 <= main_~x~4 && main_~x~4 + 4294967296 == 30) && main_~x~4 < 0;
    __VERIFIER_assert_#in~cond := 0;
    goto loc3;
  loc2_1:
    assume (main_~x~4 < 4294967296 && 0 <= main_~x~4) && !(main_~x~4 == 30);
    __VERIFIER_assert_#in~cond := 1;
    goto loc3;
  loc3:
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume !(__VERIFIER_assert_~cond == 0);
    goto loc1;
  loc4_1:
    assume __VERIFIER_assert_~cond == 0;
    goto loc5;
  loc5:
    assert false;
}

