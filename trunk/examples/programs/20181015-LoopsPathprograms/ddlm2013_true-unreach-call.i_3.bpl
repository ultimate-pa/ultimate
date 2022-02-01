procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#t~nondet1 : int;
    var main_~a~0 : int;
    var main_~flag~0 : int;
    var main_~j~0 : int;
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_#t~nondet2 : int;
    var main_#t~post3 : int;
    var main_~i~0 : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~b~0 : int;
    var main_#t~post4 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet1, main_~a~0, main_~flag~0, main_~j~0, main_#t~nondet2, main_#t~post3, main_~i~0, main_~b~0, main_#t~post4;
    havoc main_~i~0;
    havoc main_~j~0;
    havoc main_~a~0;
    havoc main_~b~0;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    main_~flag~0 := main_#t~nondet1;
    havoc main_#t~nondet1;
    main_~a~0 := 0;
    main_~b~0 := 0;
    main_~j~0 := 1;
    assume !(main_~flag~0 == 0);
    main_~i~0 := 0;
    goto loc1;
  loc1:
    assume 0 <= main_#t~nondet2 + 2147483648 && main_#t~nondet2 <= 2147483647;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume 0 == main_#t~nondet2;
    havoc main_#t~nondet2;
    assume !(main_~flag~0 == 0);
    __VERIFIER_assert_#in~cond := (if main_~a~0 % 4294967296 == main_~b~0 % 4294967296 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume 0 == __VERIFIER_assert_~cond;
    goto loc3;
  loc2_1:
    assume !(0 == main_#t~nondet2);
    havoc main_#t~nondet2;
    main_#t~post3 := main_~a~0;
    main_~a~0 := main_#t~post3 + 1;
    havoc main_#t~post3;
    main_~b~0 := main_~b~0 + -1 * main_~i~0 + main_~j~0;
    main_~i~0 := main_~i~0 + 2;
    assume (if main_~i~0 % 4294967296 < 0 && !(0 == main_~i~0 % 2) then main_~i~0 % 2 + -2 else main_~i~0 % 2) % 4294967296 == 0;
    main_~j~0 := main_~j~0 + 2;
    goto loc1;
  loc3:
    assert false;
}

