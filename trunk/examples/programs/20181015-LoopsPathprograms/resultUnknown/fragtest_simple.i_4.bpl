procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_~k~0 : int;
    var main_#t~nondet1 : int;
    var main_~j~0 : int;
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_#t~nondet2 : int;
    var main_#t~nondet3 : int;
    var main_~n~0 : int;
    var main_~i~0 : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~tmp___1~0 : int;
    var main_~pvlen~0 : int;

  loc0:
    havoc main_#res;
    havoc main_~k~0, main_#t~nondet1, main_~j~0, main_#t~nondet2, main_#t~nondet3, main_~n~0, main_~i~0, main_~tmp___1~0, main_~pvlen~0;
    havoc main_~i~0;
    havoc main_~pvlen~0;
    havoc main_~tmp___1~0;
    main_~k~0 := 0;
    havoc main_~n~0;
    main_~i~0 := 0;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    main_~pvlen~0 := main_#t~nondet1;
    havoc main_#t~nondet1;
    assume 0 <= main_#t~nondet2 + 2147483648 && main_#t~nondet2 <= 2147483647;
    assume !(main_~i~0 <= 1000000) || 0 == main_#t~nondet2;
    havoc main_#t~nondet2;
    assume !(main_~pvlen~0 < main_~i~0);
    main_~i~0 := 0;
    goto loc1;
  loc1:
    assume 0 <= main_#t~nondet3 + 2147483648 && main_#t~nondet3 <= 2147483647;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume 0 == main_#t~nondet3 || !(main_~i~0 <= 1000000);
    havoc main_#t~nondet3;
    main_~j~0 := 0;
    main_~n~0 := main_~i~0;
    goto loc3;
  loc2_1:
    assume !(0 == main_#t~nondet3) && main_~i~0 <= 1000000;
    havoc main_#t~nondet3;
    main_~tmp___1~0 := main_~i~0;
    main_~i~0 := main_~i~0 + 1;
    main_~k~0 := main_~k~0 + 1;
    goto loc1;
  loc3:
    __VERIFIER_assert_#in~cond := (if 0 <= main_~k~0 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume 0 == __VERIFIER_assert_~cond;
    goto loc5;
  loc4_1:
    assume !(0 == __VERIFIER_assert_~cond);
    main_~k~0 := main_~k~0 + -1;
    main_~i~0 := main_~i~0 + -1;
    main_~j~0 := main_~j~0 + 1;
    assume !(main_~n~0 <= main_~j~0);
    goto loc3;
  loc5:
    assert false;
}

