function { :overapproximation "shiftLeft" } ~shiftLeft(in0 : int, in1 : int) returns (out : int);
function { :overapproximation "bitwiseAnd" } ~bitwiseAnd(in0 : int, in1 : int) returns (out : int);
implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~nondet0 : int;
    var main_~i~6 : int;
    var main_~bit~6 : int;
    var main_~x~5 : int;
    var main_~y~5 : int;
    var main_~c~5 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet0, main_~i~6, main_~bit~6, main_~x~5, main_~y~5, main_~c~5;
    main_~x~5 := main_#t~nondet0;
    havoc main_#t~nondet0;
    havoc main_~y~5;
    havoc main_~c~5;
    main_~y~5 := 0;
    main_~c~5 := 0;
    goto loc1;
  loc1:
    assume true;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~c~5 % 256 < 8);
    __VERIFIER_assert_#in~cond := (if main_~x~5 % 256 == main_~y~5 % 256 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc3;
  loc2_1:
    assume !!(main_~c~5 % 256 < 8);
    main_~i~6 := ~shiftLeft(1, main_~c~5 % 256);
    main_~bit~6 := ~bitwiseAnd(main_~x~5 % 256, main_~i~6 % 256);
    assume main_~bit~6 % 256 != 0;
    main_~y~5 := main_~y~5 % 256 + main_~i~6 % 256;
    main_~c~5 := main_~c~5 % 256 + 1;
    goto loc1;
  loc3:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

