procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_~j~4 : int;
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~i~4 : int;

  loc0:
    havoc main_#res;
    havoc main_~j~4, main_~i~4;
    havoc main_~i~4;
    havoc main_~j~4;
    main_~i~4 := 1;
    main_~j~4 := 10;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume main_~i~4 <= main_~j~4;
    main_~i~4 := main_~i~4 + 2;
    main_~j~4 := main_~j~4 + -1;
    goto loc1;
  loc2_1:
    assume !(main_~i~4 <= main_~j~4);
    assume !(main_~j~4 == 6);
    __VERIFIER_assert_#in~cond := 0;
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    goto loc3;
  loc3:
    assert false;
}

