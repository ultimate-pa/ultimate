procedure ULTIMATE.start() returns ()
modifies ;
{
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_~x~4 : int;
    var main_#t~post1 : int;
    var main_#t~post0 : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~y~4 : int;

  loc0:
    havoc main_#res;
    havoc main_~x~4, main_#t~post1, main_#t~post0, main_~y~4;
    main_~x~4 := 0;
    main_~y~4 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume main_~x~4 < 4294967296 && !(main_~x~4 < 268435455);
    assume ((((0 <= main_~x~4 % 2 + 4294967294 && 0 <= main_~x~4) && 2 + 2 <= main_~x~4) && main_~x~4 < 4294967296) && main_~x~4 % 2 < 2) && !(main_~x~4 % 2 == 0);
    __VERIFIER_assert_#in~cond := 0;
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    goto loc3;
  loc2_1:
    assume main_~x~4 < 268435455 && 0 <= main_~x~4;
    main_~y~4 := 0;
    goto loc4;
  loc3:
    assert false;
  loc4:
    goto loc5;
  loc5:
    goto loc5_0, loc5_1;
  loc5_0:
    assume 0 <= main_~y~4 && main_~y~4 < 10;
    main_#t~post0 := main_~y~4;
    main_~y~4 := main_#t~post0 + 1;
    havoc main_#t~post0;
    goto loc4;
  loc5_1:
    assume main_~y~4 < 4294967296 && !(main_~y~4 < 10);
    main_#t~post1 := main_~x~4;
    main_~x~4 := main_#t~post1 + 1;
    havoc main_#t~post1;
    goto loc1;
}

