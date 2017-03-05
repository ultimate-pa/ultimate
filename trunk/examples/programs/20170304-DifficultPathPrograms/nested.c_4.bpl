var ~last : int;

implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~ret0 : int;
    var main_#t~post1 : int;
    var main_~a~5 : int;
    var main_~b~5 : int;
    var main_~c~5 : int;
    var main_~st~5 : int;
    var nondet_#res : int;
    var nondet_~x~4 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    ~last := 0;
    havoc main_#res;
    havoc main_#t~ret0, main_#t~post1, main_~a~5, main_~b~5, main_~c~5, main_~st~5;
    havoc nondet_#res;
    havoc nondet_~x~4;
    havoc nondet_~x~4;
    nondet_#res := nondet_~x~4;
    main_#t~ret0 := nondet_#res;
    assume -2147483648 <= main_#t~ret0 && main_#t~ret0 <= 2147483647;
    ~last := main_#t~ret0;
    havoc main_#t~ret0;
    main_~a~5 := 0;
    main_~b~5 := 0;
    main_~c~5 := 0;
    main_~st~5 := 0;
    assume true;
    assume !false;
    main_~st~5 := 1;
    main_~c~5 := 0;
    goto loc1;
  loc1:
    assume true;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~c~5 < 200000);
    assume main_~st~5 == 0 && main_~c~5 == ~last + 1;
    main_~a~5 := main_~a~5 + 3;
    main_~b~5 := main_~b~5 + 3;
    assume !(main_~c~5 == ~last && main_~st~5 == 0);
    __VERIFIER_assert_#in~cond := (if main_~a~5 == main_~b~5 && main_~c~5 == 200000 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc3;
  loc2_1:
    assume !!(main_~c~5 < 200000);
    assume main_~c~5 == ~last;
    main_~st~5 := 0;
    main_#t~post1 := main_~c~5;
    main_~c~5 := main_#t~post1 + 1;
    havoc main_#t~post1;
    goto loc1;
  loc3:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ~last, ~last;
modifies ~last;

