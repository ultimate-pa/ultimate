procedure ULTIMATE.start() returns ()
modifies ;
{
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_#t~post3 : int;
    var main_~y~0 : int;
    var main_#t~post2 : int;
    var main_#t~post1 : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~x~0 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~post3, main_~y~0, main_#t~post2, main_#t~post1, main_~x~0;
    havoc main_~x~0;
    havoc main_~y~0;
    main_~x~0 := 0;
    main_~y~0 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume main_~x~0 < 50;
    main_#t~post1 := main_~y~0;
    main_~y~0 := main_#t~post1 + 1;
    havoc main_#t~post1;
    goto loc3;
  loc2_1:
    assume !(main_~x~0 < 50);
    main_#t~post2 := main_~y~0;
    main_~y~0 := main_#t~post2 + -1;
    havoc main_#t~post2;
    goto loc3;
  loc3:
    goto loc3_0, loc3_1;
  loc3_0:
    assume main_~y~0 < 0;
    __VERIFIER_assert_#in~cond := (if main_~x~0 == 100 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume 0 == __VERIFIER_assert_~cond;
    goto loc4;
  loc3_1:
    assume !(main_~y~0 < 0);
    main_#t~post3 := main_~x~0;
    main_~x~0 := main_#t~post3 + 1;
    havoc main_#t~post3;
    goto loc1;
  loc4:
    assert false;
}

