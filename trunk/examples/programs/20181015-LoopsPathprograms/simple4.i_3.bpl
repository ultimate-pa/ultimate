procedure ULTIMATE.start() returns ()
modifies ;
{
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~x~0 : int;

  loc0:
    havoc main_#res;
    havoc main_~x~0;
    main_~x~0 := 268435441;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(1 < main_~x~0 % 4294967296);
    assume (!(main_~x~0 % 4294967296 < 0) || main_~x~0 % 2 == 0) || (!(main_~x~0 % 2 == 0) && main_~x~0 % 4294967296 < 0);
    __VERIFIER_assert_#in~cond := (if 0 == (if main_~x~0 % 4294967296 < 0 && !(0 == main_~x~0 % 2) then main_~x~0 % 2 + -2 else main_~x~0 % 2) % 4294967296 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume 0 == __VERIFIER_assert_~cond;
    goto loc3;
  loc2_1:
    assume 1 < main_~x~0 % 4294967296;
    main_~x~0 := main_~x~0 + -2;
    goto loc1;
  loc3:
    assert false;
}

