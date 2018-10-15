procedure ULTIMATE.start() returns ()
modifies ;
{
    var f_#res : int;
    var main_#t~ret0 : int;
    var __VERIFIER_assert_~cond : int;
    var f_~z : int;
    var main_#res : int;
    var __VERIFIER_assert_#in~cond : int;
    var f_#in~z : int;
    var main_~x~0 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~ret0, main_~x~0;
    main_~x~0 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~x~0 % 4294967296 < 268435455);
    assume (!(main_~x~0 % 4294967296 < 0) || main_~x~0 % 2 == 0) || (!(main_~x~0 % 2 == 0) && main_~x~0 % 4294967296 < 0);
    __VERIFIER_assert_#in~cond := (if 0 == (if main_~x~0 % 4294967296 < 0 && !(0 == main_~x~0 % 2) then main_~x~0 % 2 + -2 else main_~x~0 % 2) % 4294967296 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume 0 == __VERIFIER_assert_~cond;
    goto loc3;
  loc2_1:
    assume main_~x~0 % 4294967296 < 268435455;
    f_#in~z := main_~x~0;
    havoc f_#res;
    havoc f_~z;
    f_~z := f_#in~z;
    f_#res := f_~z + 2;
    main_#t~ret0 := f_#res;
    main_~x~0 := main_#t~ret0;
    havoc main_#t~ret0;
    goto loc1;
  loc3:
    assert false;
}

