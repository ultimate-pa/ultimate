implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~nondet0 : int;
    var main_#t~nondet2 : int;
    var main_#t~post1 : int;
    var main_~SIZE~5 : int;
    var main_~j~5 : int;
    var main_~k~5 : int;
    var main_~array~5 : [int]int;
    var main_~menor~5 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet0, main_#t~nondet2, main_#t~post1, main_~SIZE~5, main_~j~5, main_~k~5, main_~array~5, main_~menor~5;
    main_~SIZE~5 := 1;
    havoc main_~j~5;
    havoc main_~k~5;
    havoc main_~array~5;
    havoc main_~menor~5;
    assume -2147483648 <= main_#t~nondet0 && main_#t~nondet0 <= 2147483647;
    main_~menor~5 := main_#t~nondet0;
    havoc main_#t~nondet0;
    main_~j~5 := 0;
    goto loc1;
  loc1:
    assume true;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~j~5 % 4294967296 < main_~SIZE~5 % 4294967296);
    __VERIFIER_assert_#in~cond := (if main_~array~5[0] >= main_~menor~5 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc3;
  loc2_1:
    assume !!(main_~j~5 % 4294967296 < main_~SIZE~5 % 4294967296);
    assume -2147483648 <= main_#t~nondet2 && main_#t~nondet2 <= 2147483647;
    main_~array~5 := main_~array~5[main_~j~5 % 4294967296 := main_#t~nondet2];
    havoc main_#t~nondet2;
    assume main_~array~5[main_~j~5 % 4294967296] <= main_~menor~5;
    main_~menor~5 := main_~array~5[main_~j~5 % 4294967296];
    main_#t~post1 := main_~j~5;
    main_~j~5 := main_#t~post1 + 1;
    havoc main_#t~post1;
    goto loc1;
  loc3:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

