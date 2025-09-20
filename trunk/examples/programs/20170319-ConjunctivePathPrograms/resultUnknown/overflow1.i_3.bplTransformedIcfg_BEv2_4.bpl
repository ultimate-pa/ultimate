procedure ULTIMATE.start() returns ()
modifies ;
{
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_~x~4 : int;
    var __VERIFIER_assert_#in~cond : int;

  loc0:
    havoc main_#res;
    havoc main_~x~4;
    main_~x~4 := 10;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume 10 <= main_~x~4 && main_~x~4 < 4294967296;
    main_~x~4 := main_~x~4 + 2;
    goto loc1;
  loc2_1:
    assume !(4294967306 <= main_~x~4) && 4294967296 <= main_~x~4;
    assume ((((0 <= main_~x~4 % 2 + 4294967294 && main_~x~4 < 4294967296 + 4294967296) && main_~x~4 % 2 <= 2147483647) && 2 + 2 <= main_~x~4) && 4294967296 <= main_~x~4) && main_~x~4 % 2 < 2;
    __VERIFIER_assert_#in~cond := main_~x~4 % 2;
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    goto loc3;
  loc3:
    assert false;
}

