procedure ULTIMATE.start() returns ()
modifies ;
{
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_#t~post1 : int;
    var main_~i~0 : int;
    var __VERIFIER_assert_#in~cond : int;

  loc0:
    havoc main_#res;
    havoc main_#t~post1, main_~i~0;
    havoc main_~i~0;
    main_~i~0 := 0;
    goto loc1;
  loc1:
    assume !(1000000 == main_~i~0);
    __VERIFIER_assert_#in~cond := (if main_~i~0 <= 1000000 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume 0 == __VERIFIER_assert_~cond;
    goto loc3;
  loc2_1:
    assume !(0 == __VERIFIER_assert_~cond);
    main_#t~post1 := main_~i~0;
    main_~i~0 := main_#t~post1 + 1;
    havoc main_#t~post1;
    goto loc1;
  loc3:
    assert false;
}

