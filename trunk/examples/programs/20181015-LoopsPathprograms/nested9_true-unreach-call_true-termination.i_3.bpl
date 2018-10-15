var ~__BLAST_NONDET~0 : int;

procedure ULTIMATE.start() returns ()
modifies ~__BLAST_NONDET~0;
{
    var main_~k~0 : int;
    var main_#t~nondet1 : int;
    var __VERIFIER_assert_~cond : int;
    var main_#t~nondet2 : int;
    var main_#t~nondet3 : int;
    var main_~m~0 : int;
    var main_~n~0 : int;
    var main_~i~0 : int;
    var main_#t~post6 : int;
    var main_#t~post5 : int;
    var main_#t~post4 : int;
    var main_~j~0 : int;
    var main_#res : int;
    var main_~l~0 : int;
    var __VERIFIER_assert_#in~cond : int;

  loc0:
    ~__BLAST_NONDET~0 := 0;
    havoc main_#res;
    havoc main_~k~0, main_#t~nondet1, main_~j~0, main_#t~nondet2, main_~l~0, main_#t~nondet3, main_~m~0, main_~n~0, main_~i~0, main_#t~post6, main_#t~post5, main_#t~post4;
    havoc main_~i~0;
    havoc main_~j~0;
    havoc main_~k~0;
    havoc main_~n~0;
    havoc main_~l~0;
    havoc main_~m~0;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    main_~n~0 := main_#t~nondet1;
    havoc main_#t~nondet1;
    assume 0 <= main_#t~nondet2 + 2147483648 && main_#t~nondet2 <= 2147483647;
    main_~m~0 := main_#t~nondet2;
    havoc main_#t~nondet2;
    assume 0 <= main_#t~nondet3 + 2147483648 && main_#t~nondet3 <= 2147483647;
    main_~l~0 := main_#t~nondet3;
    havoc main_#t~nondet3;
    assume main_~n~0 < 1000000 && 0 < main_~n~0 + 1000000;
    assume main_~m~0 < 1000000 && 0 < main_~m~0 + 1000000;
    assume main_~l~0 < 1000000 && 0 < main_~l~0 + 1000000;
    assume 3 * main_~n~0 <= main_~l~0 + main_~m~0;
    main_~i~0 := 0;
    goto loc1;
  loc1:
    assume main_~i~0 < main_~n~0;
    main_~j~0 := 2 * main_~i~0;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~j~0 < 3 * main_~i~0);
    main_#t~post4 := main_~i~0;
    main_~i~0 := main_#t~post4 + 1;
    havoc main_#t~post4;
    goto loc1;
  loc2_1:
    assume main_~j~0 < 3 * main_~i~0;
    main_~k~0 := main_~i~0;
    goto loc3;
  loc3:
    assume main_~k~0 < main_~j~0;
    __VERIFIER_assert_#in~cond := (if main_~k~0 <= 2 * main_~n~0 + main_~i~0 then 1 else 0);
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
    main_#t~post6 := main_~k~0;
    main_~k~0 := main_#t~post6 + 1;
    havoc main_#t~post6;
    goto loc3;
  loc5:
    assert false;
}

