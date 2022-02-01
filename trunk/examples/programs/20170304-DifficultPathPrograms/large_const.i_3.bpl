implementation ULTIMATE.start() returns (){
    var #in~argc : int, #in~argv.base : int, #in~argv.offset : int;
    var main_#in~argc : int;
    var main_#in~argv.base : int, main_#in~argv.offset : int;
    var main_#res : int;
    var main_#t~nondet0 : int;
    var main_#t~post1 : int;
    var main_#t~nondet2 : int;
    var main_#t~post3 : int;
    var main_#t~post4 : int;
    var main_~argc : int;
    var main_~argv.base : int, main_~argv.offset : int;
    var main_~c1~5 : int;
    var main_~c2~5 : int;
    var main_~c3~5 : int;
    var main_~n~5 : int;
    var main_~v~5 : int;
    var main_~i~5 : int;
    var main_~k~5 : int;
    var main_~j~5 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    main_#in~argc, main_#in~argv.base, main_#in~argv.offset := #in~argc, #in~argv.base, #in~argv.offset;
    havoc main_#res;
    havoc main_#t~nondet0, main_#t~post1, main_#t~nondet2, main_#t~post3, main_#t~post4, main_~argc, main_~argv.base, main_~argv.offset, main_~c1~5, main_~c2~5, main_~c3~5, main_~n~5, main_~v~5, main_~i~5, main_~k~5, main_~j~5;
    main_~argc := main_#in~argc;
    main_~argv.base, main_~argv.offset := main_#in~argv.base, main_#in~argv.offset;
    main_~c1~5 := 4000;
    main_~c2~5 := 2000;
    main_~c3~5 := 10000;
    havoc main_~n~5;
    havoc main_~v~5;
    havoc main_~i~5;
    havoc main_~k~5;
    havoc main_~j~5;
    assume -2147483648 <= main_#t~nondet0 && main_#t~nondet0 <= 2147483647;
    main_~n~5 := main_#t~nondet0;
    havoc main_#t~nondet0;
    assume !!(0 <= main_~n~5 && main_~n~5 < 10);
    main_~k~5 := 0;
    main_~i~5 := 0;
    goto loc1;
  loc1:
    assume true;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~i~5 < main_~n~5);
    main_~j~5 := 0;
    assume true;
    assume !!(main_~j~5 < main_~n~5);
    __VERIFIER_assert_#in~cond := (if main_~k~5 > 0 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc3;
  loc2_1:
    assume !!(main_~i~5 < main_~n~5);
    main_#t~post1 := main_~i~5;
    main_~i~5 := main_#t~post1 + 1;
    havoc main_#t~post1;
    assume -2147483648 <= main_#t~nondet2 && main_#t~nondet2 <= 2147483647;
    main_~v~5 := main_#t~nondet2;
    havoc main_#t~nondet2;
    assume !!(0 <= main_~v~5 && main_~n~5 < 2);
    assume main_~v~5 == 0;
    main_~k~5 := main_~k~5 + main_~c1~5;
    goto loc1;
  loc3:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

