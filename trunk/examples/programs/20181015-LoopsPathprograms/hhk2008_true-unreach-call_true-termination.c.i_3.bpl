procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#t~nondet1 : int;
    var main_~a~0 : int;
    var main_~res~0 : int;
    var main_~cnt~0 : int;
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_#t~nondet2 : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~b~0 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet1, main_~a~0, main_~res~0, main_~cnt~0, main_#t~nondet2, main_~b~0;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    main_~a~0 := main_#t~nondet1;
    havoc main_#t~nondet1;
    assume 0 <= main_#t~nondet2 + 2147483648 && main_#t~nondet2 <= 2147483647;
    main_~b~0 := main_#t~nondet2;
    havoc main_#t~nondet2;
    havoc main_~res~0;
    havoc main_~cnt~0;
    assume main_~a~0 <= 1000000;
    assume 0 <= main_~b~0 && main_~b~0 <= 1000000;
    main_~res~0 := main_~a~0;
    main_~cnt~0 := main_~b~0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(0 < main_~cnt~0);
    __VERIFIER_assert_#in~cond := (if main_~res~0 == main_~a~0 + main_~b~0 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume 0 == __VERIFIER_assert_~cond;
    goto loc3;
  loc2_1:
    assume 0 < main_~cnt~0;
    main_~cnt~0 := main_~cnt~0 + -1;
    main_~res~0 := main_~res~0 + 1;
    goto loc1;
  loc3:
    assert false;
}

