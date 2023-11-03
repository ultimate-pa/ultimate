procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#t~nondet1 : int;
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_~y~0 : int;
    var main_#t~post2 : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~x~0 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet1, main_~y~0, main_#t~post2, main_~x~0;
    main_~x~0 := 1;
    main_~y~0 := main_#t~nondet1;
    havoc main_#t~nondet1;
    assume 0 < main_~y~0 % 4294967296;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~x~0 % 4294967296 < main_~y~0 % 4294967296);
    __VERIFIER_assert_#in~cond := (if main_~y~0 % 4294967296 == main_~x~0 % 4294967296 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume 0 == __VERIFIER_assert_~cond;
    goto loc3;
  loc2_1:
    assume main_~x~0 % 4294967296 < main_~y~0 % 4294967296;
    assume !(main_~x~0 % 4294967296 < (if main_~y~0 % 4294967296 < 0 && !(main_~y~0 % 4294967296 % (main_~x~0 % 4294967296) == 0) then (if main_~x~0 % 4294967296 < 0 then main_~y~0 % 4294967296 / (main_~x~0 % 4294967296) + -1 else main_~y~0 % 4294967296 / (main_~x~0 % 4294967296) + 1) else main_~y~0 % 4294967296 / (main_~x~0 % 4294967296)) % 4294967296);
    main_#t~post2 := main_~x~0;
    main_~x~0 := main_#t~post2 + 1;
    havoc main_#t~post2;
    goto loc1;
  loc3:
    assert false;
}

