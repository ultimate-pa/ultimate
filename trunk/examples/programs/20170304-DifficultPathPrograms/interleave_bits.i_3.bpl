function { :overapproximation "shiftLeft" } ~shiftLeft(in0 : int, in1 : int) returns (out : int);
function { :overapproximation "bitwiseAnd" } ~bitwiseAnd(in0 : int, in1 : int) returns (out : int);
function { :overapproximation "bitwiseOr" } ~bitwiseOr(in0 : int, in1 : int) returns (out : int);
implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~nondet0 : int;
    var main_#t~nondet1 : int;
    var main_~x~5 : int;
    var main_~y~5 : int;
    var main_~xx~5 : int;
    var main_~yy~5 : int;
    var main_~zz~5 : int;
    var main_~z~5 : int;
    var main_~i~5 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet0, main_#t~nondet1, main_~x~5, main_~y~5, main_~xx~5, main_~yy~5, main_~zz~5, main_~z~5, main_~i~5;
    main_~x~5 := main_#t~nondet0;
    havoc main_#t~nondet0;
    main_~y~5 := main_#t~nondet1;
    havoc main_#t~nondet1;
    havoc main_~xx~5;
    havoc main_~yy~5;
    havoc main_~zz~5;
    main_~z~5 := 0;
    main_~i~5 := 0;
    goto loc1;
  loc1:
    assume true;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~i~5 % 4294967296 < 16);
    main_~xx~5 := main_~x~5 % 65536;
    main_~yy~5 := main_~y~5 % 65536;
    main_~xx~5 := ~bitwiseAnd(~bitwiseOr(main_~xx~5, ~shiftLeft(main_~xx~5, 8)), 16711935);
    main_~xx~5 := ~bitwiseAnd(~bitwiseOr(main_~xx~5, ~shiftLeft(main_~xx~5, 4)), 252645135);
    main_~xx~5 := ~bitwiseAnd(~bitwiseOr(main_~xx~5, ~shiftLeft(main_~xx~5, 2)), 858993459);
    main_~xx~5 := ~bitwiseAnd(~bitwiseOr(main_~xx~5, ~shiftLeft(main_~xx~5, 1)), 1431655765);
    main_~yy~5 := ~bitwiseAnd(~bitwiseOr(main_~yy~5, ~shiftLeft(main_~yy~5, 8)), 16711935);
    main_~yy~5 := ~bitwiseAnd(~bitwiseOr(main_~yy~5, ~shiftLeft(main_~yy~5, 4)), 252645135);
    main_~yy~5 := ~bitwiseAnd(~bitwiseOr(main_~yy~5, ~shiftLeft(main_~yy~5, 2)), 858993459);
    main_~yy~5 := ~bitwiseAnd(~bitwiseOr(main_~yy~5, ~shiftLeft(main_~yy~5, 1)), 1431655765);
    main_~zz~5 := ~bitwiseOr(main_~xx~5, ~shiftLeft(main_~yy~5, 1));
    __VERIFIER_assert_#in~cond := (if main_~z~5 % 4294967296 == main_~zz~5 % 4294967296 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc3;
  loc2_1:
    assume !!(main_~i~5 % 4294967296 < 16);
    main_~z~5 := ~bitwiseOr(main_~z~5, ~bitwiseOr(~shiftLeft(~bitwiseAnd(main_~x~5 % 65536, ~shiftLeft(1, main_~i~5)), main_~i~5), ~shiftLeft(~bitwiseAnd(main_~y~5 % 65536, ~shiftLeft(1, main_~i~5)), main_~i~5 + 1)));
    main_~i~5 := main_~i~5 + 1;
    goto loc1;
  loc3:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

