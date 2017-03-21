procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#t~nondet0 : int;
    var main_~yy~5 : int;
    var main_~z~5 : int;
    var main_#t~nondet1 : int;
    var main_~xx~5 : int;
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_~x~5 : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~y~5 : int;
    var main_~zz~5 : int;
    var main_~i~5 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet0, main_~yy~5, main_~z~5, main_#t~nondet1, main_~xx~5, main_~x~5, main_~y~5, main_~zz~5, main_~i~5;
    main_~x~5 := main_#t~nondet0;
    havoc main_#t~nondet0;
    main_~y~5 := main_#t~nondet1;
    havoc main_#t~nondet1;
    havoc main_~xx~5;
    havoc main_~yy~5;
    havoc main_~zz~5;
    main_~z~5 := 0;
    main_~i~5 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume main_~i~5 < 4294967296 && !(main_~i~5 < 16);
    assume main_~x~5 < -65536;
    main_~xx~5 := main_~x~5 % 65536;
    assume main_~y~5 < -65536;
    main_~yy~5 := main_~y~5 % 65536;
    havoc main_~xx~5;
    havoc main_~xx~5;
    havoc main_~xx~5;
    havoc main_~xx~5;
    havoc main_~yy~5;
    havoc main_~yy~5;
    havoc main_~yy~5;
    havoc main_~yy~5;
    havoc main_~zz~5;
    assume (((main_~zz~5 < 4294967296 && 0 <= main_~zz~5) && -4294967296 <= main_~z~5) && main_~z~5 < 0) && !(main_~z~5 + 4294967296 == main_~zz~5);
    __VERIFIER_assert_#in~cond := 0;
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    goto loc3;
  loc2_1:
    assume 0 <= main_~i~5 && main_~i~5 < 16;
    havoc main_~z~5;
    main_~i~5 := main_~i~5 + 1;
    goto loc1;
  loc3:
    assert false;
}

