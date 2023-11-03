procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#t~nondet0 : int;
    var main_~sn~0 : int;
    var main_~j~0 : int;
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_~n~0 : int;
    var main_#t~post2 : int;
    var main_#t~post1 : int;
    var main_~i~0 : int;
    var __VERIFIER_assert_#in~cond : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet0, main_~sn~0, main_~j~0, main_~n~0, main_#t~post2, main_#t~post1, main_~i~0;
    havoc main_~i~0;
    main_~j~0 := 10;
    main_~n~0 := (if main_#t~nondet0 % 4294967296 <= 2147483647 then main_#t~nondet0 % 4294967296 else main_#t~nondet0 % 4294967296 + -4294967296);
    havoc main_#t~nondet0;
    main_~sn~0 := 0;
    main_~i~0 := 1;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~i~0 <= main_~n~0);
    assume (0 == main_~sn~0 || 2 * main_~n~0 == main_~sn~0) || (!(0 == main_~sn~0) && !(2 * main_~n~0 == main_~sn~0));
    __VERIFIER_assert_#in~cond := (if main_~sn~0 == 2 * main_~n~0 || main_~sn~0 == 0 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume 0 == __VERIFIER_assert_~cond;
    goto loc3;
  loc2_1:
    assume main_~i~0 <= main_~n~0;
    assume main_~i~0 < main_~j~0;
    main_~sn~0 := main_~sn~0 + 2;
    main_#t~post2 := main_~j~0;
    main_~j~0 := main_#t~post2 + -1;
    havoc main_#t~post2;
    main_#t~post1 := main_~i~0;
    main_~i~0 := main_#t~post1 + 1;
    havoc main_#t~post1;
    goto loc1;
  loc3:
    assert false;
}

