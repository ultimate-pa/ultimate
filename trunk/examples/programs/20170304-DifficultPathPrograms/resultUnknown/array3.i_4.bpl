implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~nondet1 : int;
    var main_#t~post0 : int;
    var main_#t~post2 : int;
    var main_~A~5 : [int]int;
    var main_~i~5 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet1, main_#t~post0, main_#t~post2, main_~A~5, main_~i~5;
    havoc main_~A~5;
    havoc main_~i~5;
    main_~i~5 := 0;
    goto loc1;
  loc1:
    assume true;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~i~5 < 1024);
    main_~i~5 := 0;
    goto loc3;
  loc2_1:
    assume !!(main_~i~5 < 1024);
    assume -2147483648 <= main_#t~nondet1 && main_#t~nondet1 <= 2147483647;
    main_~A~5 := main_~A~5[main_~i~5 := main_#t~nondet1];
    havoc main_#t~nondet1;
    main_#t~post0 := main_~i~5;
    main_~i~5 := main_#t~post0 + 1;
    havoc main_#t~post0;
    goto loc1;
  loc3:
    assume true;
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume !(main_~A~5[main_~i~5] != 0 && main_~i~5 < 1024);
    __VERIFIER_assert_#in~cond := (if main_~i~5 <= 512 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc5;
  loc4_1:
    assume !!(main_~A~5[main_~i~5] != 0 && main_~i~5 < 1024);
    main_#t~post2 := main_~i~5;
    main_~i~5 := main_#t~post2 + 1;
    havoc main_#t~post2;
    goto loc3;
  loc5:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

