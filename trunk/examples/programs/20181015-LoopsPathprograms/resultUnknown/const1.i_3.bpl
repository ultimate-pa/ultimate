procedure ULTIMATE.start() returns ()
modifies ;
{
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_~y~0 : int;
    var main_#t~post0 : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~x~0 : int;

  loc0:
    havoc main_#res;
    havoc main_~y~0, main_#t~post0, main_~x~0;
    main_~x~0 := 1;
    main_~y~0 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~y~0 % 4294967296 < 1024);
    __VERIFIER_assert_#in~cond := (if 1 == main_~x~0 % 4294967296 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume 0 == __VERIFIER_assert_~cond;
    goto loc3;
  loc2_1:
    assume main_~y~0 % 4294967296 < 1024;
    main_~x~0 := 0;
    main_#t~post0 := main_~y~0;
    main_~y~0 := main_#t~post0 + 1;
    havoc main_#t~post0;
    goto loc1;
  loc3:
    assert false;
}

