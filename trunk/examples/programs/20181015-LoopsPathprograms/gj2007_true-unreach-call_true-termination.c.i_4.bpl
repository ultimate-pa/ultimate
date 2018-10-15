procedure ULTIMATE.start() returns ()
modifies ;
{
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_~y~0 : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~x~0 : int;

  loc0:
    havoc main_#res;
    havoc main_~y~0, main_~x~0;
    main_~x~0 := 0;
    main_~y~0 := 50;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~x~0 < 100);
    __VERIFIER_assert_#in~cond := (if main_~y~0 == 100 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume 0 == __VERIFIER_assert_~cond;
    goto loc3;
  loc2_1:
    assume main_~x~0 < 100;
    goto loc4;
  loc3:
    assert false;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume main_~x~0 < 50;
    main_~x~0 := main_~x~0 + 1;
    goto loc1;
  loc4_1:
    assume !(main_~x~0 < 50);
    main_~x~0 := main_~x~0 + 1;
    main_~y~0 := main_~y~0 + 1;
    goto loc1;
}

