procedure ULTIMATE.start() returns ()
modifies ;
{
    var f_#res : int;
    var main_#t~ret0 : int;
    var __VERIFIER_assert_~cond : int;
    var f_~z : int;
    var main_#res : int;
    var main_~x~5 : int;
    var __VERIFIER_assert_#in~cond : int;
    var f_#in~z : int;

  loc0:
    havoc main_#res;
    havoc main_#t~ret0, main_~x~5;
    main_~x~5 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume main_~x~5 < 4294967296 && !(main_~x~5 < 268435455);
    assume ((!(main_~x~5 < 0) && 2 + 2 <= main_~x~5) && main_~x~5 < 4294967296) && main_~x~5 % 2 <= 2147483647;
    __VERIFIER_assert_#in~cond := main_~x~5 % 2;
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    goto loc3;
  loc2_1:
    assume 0 <= main_~x~5 && main_~x~5 < 268435455;
    f_#in~z := main_~x~5;
    havoc f_#res;
    havoc f_~z;
    f_~z := f_#in~z;
    f_#res := f_~z + 2;
    main_#t~ret0 := f_#res;
    main_~x~5 := main_#t~ret0;
    havoc main_#t~ret0;
    goto loc1;
  loc3:
    assert false;
}

