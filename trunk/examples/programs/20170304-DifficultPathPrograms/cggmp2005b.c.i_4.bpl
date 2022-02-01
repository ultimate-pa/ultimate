implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_~i~4 : int;
    var main_~j~4 : int;
    var main_~k~4 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    havoc main_#res;
    havoc main_~i~4, main_~j~4, main_~k~4;
    havoc main_~i~4;
    havoc main_~j~4;
    havoc main_~k~4;
    main_~i~4 := 0;
    main_~k~4 := 9;
    main_~j~4 := -100;
    goto loc1;
  loc1:
    assume true;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~i~4 <= 100);
    __VERIFIER_assert_#in~cond := (if main_~k~4 == 4 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc3;
  loc2_1:
    assume !!(main_~i~4 <= 100);
    main_~i~4 := main_~i~4 + 1;
    goto loc4;
  loc3:
    assert false;
  loc4:
    assume true;
    goto loc5;
  loc5:
    goto loc5_0, loc5_1;
  loc5_0:
    assume !(main_~j~4 < 20);
    main_~k~4 := 4;
    assume true;
    assume !(main_~k~4 <= 3);
    goto loc1;
  loc5_1:
    assume !!(main_~j~4 < 20);
    main_~j~4 := main_~i~4 + main_~j~4;
    goto loc4;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

