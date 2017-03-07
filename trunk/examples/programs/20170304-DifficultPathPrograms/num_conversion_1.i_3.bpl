function { :overapproximation "shiftLeft" } ~shiftLeft(in0 : int, in1 : int) returns (out : int);
function { :overapproximation "bitwiseAnd" } ~bitwiseAnd(in0 : int, in1 : int) returns (out : int);
implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_~i~5 : int;
    var main_~bit~5 : int;
    var main_~x~4 : int;
    var main_~y~4 : int;
    var main_~c~4 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    havoc main_#res;
    havoc main_~i~5, main_~bit~5, main_~x~4, main_~y~4, main_~c~4;
    havoc main_~x~4;
    havoc main_~y~4;
    havoc main_~c~4;
    main_~x~4 := 37;
    main_~y~4 := 0;
    main_~c~4 := 0;
    goto loc1;
  loc1:
    assume true;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~c~4 % 256 < 8);
    __VERIFIER_assert_#in~cond := (if main_~x~4 % 256 == main_~y~4 % 256 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc3;
  loc2_1:
    assume !!(main_~c~4 % 256 < 8);
    main_~i~5 := ~shiftLeft(1, main_~c~4 % 256);
    main_~bit~5 := ~bitwiseAnd(main_~x~4 % 256, main_~i~5 % 256);
    assume main_~bit~5 % 256 != 0;
    main_~y~4 := main_~y~4 % 256 + main_~i~5 % 256;
    main_~c~4 := main_~c~4 % 256 + 1;
    goto loc1;
  loc3:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

