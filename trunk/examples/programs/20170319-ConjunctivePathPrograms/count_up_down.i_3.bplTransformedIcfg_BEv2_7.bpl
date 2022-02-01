procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#t~nondet0 : int;
    var main_~n~5 : int;
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_#t~post2 : int;
    var main_#t~post1 : int;
    var main_~x~5 : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~y~5 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet0, main_~n~5, main_#t~post2, main_#t~post1, main_~x~5, main_~y~5;
    main_~n~5 := main_#t~nondet0;
    havoc main_#t~nondet0;
    main_~x~5 := main_~n~5;
    main_~y~5 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume 4294967296 + 4294967296 <= main_~x~5 && 0 < main_~x~5 % 4294967296;
    main_#t~post1 := main_~x~5;
    main_~x~5 := main_#t~post1 - 1;
    havoc main_#t~post1;
    main_#t~post2 := main_~y~5;
    main_~y~5 := main_#t~post2 + 1;
    havoc main_#t~post2;
    goto loc1;
  loc2_1:
    assume !(0 < main_~x~5 % 4294967296) && main_~x~5 < -4294967296;
    assume ((4294967296 <= main_~y~5 && 4294967296 + 4294967296 <= main_~n~5) && !(main_~y~5 - 4294967296 == main_~n~5 % 4294967296)) && main_~y~5 < 4294967296 + 4294967296;
    __VERIFIER_assert_#in~cond := 0;
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    goto loc3;
  loc3:
    assert false;
}

