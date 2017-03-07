var ~INFINITY : int;

implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~nondet0 : int;
    var main_#t~nondet1 : int;
    var main_#t~post2 : int;
    var main_#t~post4 : int;
    var main_#t~post3 : int;
    var main_#t~post5 : int;
    var main_#t~post6 : int;
    var main_~nodecount~5 : int;
    var main_~edgecount~5 : int;
    var main_~source~5 : int;
    var main_~Source~5 : [int]int;
    var main_~Dest~5 : [int]int;
    var main_~Weight~5 : [int]int;
    var main_~distance~5 : [int]int;
    var main_~x~5 : int;
    var main_~y~5 : int;
    var main_~i~5 : int;
    var main_~j~5 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    ~INFINITY := 899;
    havoc main_#res;
    havoc main_#t~nondet0, main_#t~nondet1, main_#t~post2, main_#t~post4, main_#t~post3, main_#t~post5, main_#t~post6, main_~nodecount~5, main_~edgecount~5, main_~source~5, main_~Source~5, main_~Dest~5, main_~Weight~5, main_~distance~5, main_~x~5, main_~y~5, main_~i~5, main_~j~5;
    assume -2147483648 <= main_#t~nondet0 && main_#t~nondet0 <= 2147483647;
    main_~nodecount~5 := main_#t~nondet0;
    havoc main_#t~nondet0;
    assume -2147483648 <= main_#t~nondet1 && main_#t~nondet1 <= 2147483647;
    main_~edgecount~5 := main_#t~nondet1;
    havoc main_#t~nondet1;
    assume !!(0 <= main_~nodecount~5 && main_~nodecount~5 <= 4);
    assume !!(0 <= main_~edgecount~5 && main_~edgecount~5 <= 19);
    main_~source~5 := 0;
    main_~Source~5 := main_~Source~5[0 := 0];
    main_~Source~5 := main_~Source~5[1 := 4];
    main_~Source~5 := main_~Source~5[2 := 1];
    main_~Source~5 := main_~Source~5[3 := 1];
    main_~Source~5 := main_~Source~5[4 := 0];
    main_~Source~5 := main_~Source~5[5 := 0];
    main_~Source~5 := main_~Source~5[6 := 1];
    main_~Source~5 := main_~Source~5[7 := 3];
    main_~Source~5 := main_~Source~5[8 := 4];
    main_~Source~5 := main_~Source~5[9 := 4];
    main_~Source~5 := main_~Source~5[10 := 2];
    main_~Source~5 := main_~Source~5[11 := 2];
    main_~Source~5 := main_~Source~5[12 := 3];
    main_~Source~5 := main_~Source~5[13 := 0];
    main_~Source~5 := main_~Source~5[14 := 0];
    main_~Source~5 := main_~Source~5[15 := 3];
    main_~Source~5 := main_~Source~5[16 := 1];
    main_~Source~5 := main_~Source~5[17 := 2];
    main_~Source~5 := main_~Source~5[18 := 2];
    main_~Source~5 := main_~Source~5[19 := 3];
    main_~Dest~5 := main_~Dest~5[0 := 1];
    main_~Dest~5 := main_~Dest~5[1 := 3];
    main_~Dest~5 := main_~Dest~5[2 := 4];
    main_~Dest~5 := main_~Dest~5[3 := 1];
    main_~Dest~5 := main_~Dest~5[4 := 1];
    main_~Dest~5 := main_~Dest~5[5 := 4];
    main_~Dest~5 := main_~Dest~5[6 := 3];
    main_~Dest~5 := main_~Dest~5[7 := 4];
    main_~Dest~5 := main_~Dest~5[8 := 3];
    main_~Dest~5 := main_~Dest~5[9 := 0];
    main_~Dest~5 := main_~Dest~5[10 := 0];
    main_~Dest~5 := main_~Dest~5[11 := 0];
    main_~Dest~5 := main_~Dest~5[12 := 0];
    main_~Dest~5 := main_~Dest~5[13 := 2];
    main_~Dest~5 := main_~Dest~5[14 := 3];
    main_~Dest~5 := main_~Dest~5[15 := 0];
    main_~Dest~5 := main_~Dest~5[16 := 2];
    main_~Dest~5 := main_~Dest~5[17 := 1];
    main_~Dest~5 := main_~Dest~5[18 := 0];
    main_~Dest~5 := main_~Dest~5[19 := 4];
    main_~Weight~5 := main_~Weight~5[0 := 0];
    main_~Weight~5 := main_~Weight~5[1 := 1];
    main_~Weight~5 := main_~Weight~5[2 := 2];
    main_~Weight~5 := main_~Weight~5[3 := 3];
    main_~Weight~5 := main_~Weight~5[4 := 4];
    main_~Weight~5 := main_~Weight~5[5 := 5];
    main_~Weight~5 := main_~Weight~5[6 := 6];
    main_~Weight~5 := main_~Weight~5[7 := 7];
    main_~Weight~5 := main_~Weight~5[8 := 8];
    main_~Weight~5 := main_~Weight~5[9 := 9];
    main_~Weight~5 := main_~Weight~5[10 := 10];
    main_~Weight~5 := main_~Weight~5[11 := 11];
    main_~Weight~5 := main_~Weight~5[12 := 12];
    main_~Weight~5 := main_~Weight~5[13 := 13];
    main_~Weight~5 := main_~Weight~5[14 := 14];
    main_~Weight~5 := main_~Weight~5[15 := 15];
    main_~Weight~5 := main_~Weight~5[16 := 16];
    main_~Weight~5 := main_~Weight~5[17 := 17];
    main_~Weight~5 := main_~Weight~5[18 := 18];
    main_~Weight~5 := main_~Weight~5[19 := 19];
    havoc main_~distance~5;
    havoc main_~x~5;
    havoc main_~y~5;
    havoc main_~i~5;
    havoc main_~j~5;
    main_~i~5 := 0;
    goto loc1;
  loc1:
    assume true;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~i~5 < main_~nodecount~5);
    main_~i~5 := 0;
    goto loc3;
  loc2_1:
    assume !!(main_~i~5 < main_~nodecount~5);
    assume main_~i~5 == main_~source~5;
    main_~distance~5 := main_~distance~5[main_~i~5 := 0];
    main_#t~post2 := main_~i~5;
    main_~i~5 := main_#t~post2 + 1;
    havoc main_#t~post2;
    goto loc1;
  loc3:
    assume true;
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume !(main_~i~5 < main_~nodecount~5);
    main_~i~5 := 0;
    assume true;
    assume !(main_~i~5 < main_~edgecount~5);
    main_~i~5 := 0;
    assume true;
    assume !!(main_~i~5 < main_~nodecount~5);
    __VERIFIER_assert_#in~cond := (if main_~distance~5[main_~i~5] >= 0 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc5;
  loc4_1:
    assume !!(main_~i~5 < main_~nodecount~5);
    main_~j~5 := 0;
    assume true;
    assume !(main_~j~5 < main_~edgecount~5);
    main_#t~post3 := main_~i~5;
    main_~i~5 := main_#t~post3 + 1;
    havoc main_#t~post3;
    goto loc3;
  loc5:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ~INFINITY;
modifies ;

