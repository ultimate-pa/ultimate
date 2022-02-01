procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_~j~0 : int;
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_~i~0 : int;
    var __VERIFIER_assert_#in~cond : int;

  loc0:
    havoc main_#res;
    havoc main_~j~0, main_~i~0;
    havoc main_~i~0;
    havoc main_~j~0;
    main_~i~0 := 1;
    main_~j~0 := 10;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~i~0 <= main_~j~0);
    __VERIFIER_assert_#in~cond := (if main_~j~0 == 6 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume 0 == __VERIFIER_assert_~cond;
    goto loc3;
  loc2_1:
    assume main_~i~0 <= main_~j~0;
    main_~i~0 := main_~i~0 + 2;
    main_~j~0 := main_~j~0 + -1;
    goto loc1;
  loc3:
    assert false;
}

