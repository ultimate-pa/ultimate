procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#t~nondet0 : int;
    var main_#t~nondet1 : int;
    var main_~x~7 : int;
    var gcd_test_~a : int;
    var gcd_test_~b : int;
    var __VERIFIER_assert_~cond : int;
    var gcd_test_#in~b : int;
    var gcd_test_#in~a : int;
    var gcd_test_#res : int;
    var gcd_test_~t~5 : int;
    var main_~g~7 : int;
    var main_#t~ret2 : int;
    var main_~y~7 : int;
    var main_#res : int;
    var __VERIFIER_assert_#in~cond : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet0, main_#t~nondet1, main_#t~ret2, main_~y~7, main_~x~7, main_~g~7;
    assume 0 <= main_#t~nondet0 + 128 && main_#t~nondet0 <= 127;
    main_~x~7 := main_#t~nondet0;
    havoc main_#t~nondet0;
    assume main_#t~nondet1 <= 127 && 0 <= main_#t~nondet1 + 128;
    main_~y~7 := main_#t~nondet1;
    havoc main_#t~nondet1;
    havoc main_~g~7;
    gcd_test_#in~b, gcd_test_#in~a := main_~y~7, main_~x~7;
    havoc gcd_test_#res;
    havoc gcd_test_~a, gcd_test_~b, gcd_test_~t~5;
    gcd_test_~a := gcd_test_#in~a;
    gcd_test_~b := gcd_test_#in~b;
    havoc gcd_test_~t~5;
    assume gcd_test_~a < 0;
    assume -256 <= 255 * gcd_test_~a && 255 * gcd_test_~a < 0;
    gcd_test_~a := 255 * gcd_test_~a + 256;
    assume !(gcd_test_~b < 0);
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(gcd_test_~b == 0);
    gcd_test_~t~5 := gcd_test_~b;
    assume ((gcd_test_~a % gcd_test_~b % 256 <= 127 && 256 + 256 <= gcd_test_~b + gcd_test_~a % gcd_test_~b) && 256 + 256 <= gcd_test_~a % gcd_test_~b) && !(gcd_test_~a < 0);
    gcd_test_~b := gcd_test_~a % gcd_test_~b % 256;
    gcd_test_~a := gcd_test_~t~5;
    goto loc1;
  loc2_1:
    assume gcd_test_~b == 0;
    gcd_test_#res := gcd_test_~a;
    main_#t~ret2 := gcd_test_#res;
    assume 0 <= main_#t~ret2 + 128 && main_#t~ret2 <= 127;
    main_~g~7 := main_#t~ret2;
    havoc main_#t~ret2;
    assume 0 < main_~y~7;
    assume !(main_~g~7 <= main_~y~7);
    __VERIFIER_assert_#in~cond := 0;
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    goto loc3;
  loc3:
    assert false;
}

