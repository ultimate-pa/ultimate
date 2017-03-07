implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~ret0 : int;
    var main_~x~5 : int;
    var f_#in~z : int;
    var f_#res : int;
    var f_~z : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    havoc main_#res;
    havoc main_#t~ret0, main_~x~5;
    main_~x~5 := 0;
    goto loc1;
  loc1:
    assume true;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~x~5 % 4294967296 < 268435455);
    __VERIFIER_assert_#in~cond := (if (if main_~x~5 % 4294967296 < 0 && main_~x~5 % 4294967296 % 2 != 0 then main_~x~5 % 4294967296 % 2 - 2 else main_~x~5 % 4294967296 % 2) % 4294967296 % 4294967296 <= 2147483647 then (if main_~x~5 % 4294967296 < 0 && main_~x~5 % 4294967296 % 2 != 0 then main_~x~5 % 4294967296 % 2 - 2 else main_~x~5 % 4294967296 % 2) % 4294967296 % 4294967296 else (if main_~x~5 % 4294967296 < 0 && main_~x~5 % 4294967296 % 2 != 0 then main_~x~5 % 4294967296 % 2 - 2 else main_~x~5 % 4294967296 % 2) % 4294967296 % 4294967296 - 4294967296);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc3;
  loc2_1:
    assume !!(main_~x~5 % 4294967296 < 268435455);
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

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

