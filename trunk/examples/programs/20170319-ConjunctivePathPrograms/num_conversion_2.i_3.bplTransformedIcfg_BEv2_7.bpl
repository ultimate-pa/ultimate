procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#t~nondet0 : int;
    var main_~i~6 : int;
    var main_~bit~6 : int;
    var main_~c~5 : int;
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_~x~5 : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~y~5 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet0, main_~i~6, main_~bit~6, main_~c~5, main_~x~5, main_~y~5;
    main_~x~5 := main_#t~nondet0;
    havoc main_#t~nondet0;
    havoc main_~y~5;
    havoc main_~c~5;
    main_~y~5 := 0;
    main_~c~5 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume main_~c~5 < 256 && !(main_~c~5 < 8);
    assume (((!(main_~x~5 + 256 == main_~y~5 - 256) && -256 <= main_~x~5) && main_~y~5 < 256 + 256) && 256 <= main_~y~5) && main_~x~5 < 0;
    __VERIFIER_assert_#in~cond := 0;
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    goto loc3;
  loc2_1:
    assume 0 <= main_~c~5 && main_~c~5 < 8;
    havoc main_~i~6;
    havoc main_~bit~6;
    assume (!(main_~bit~6 == 0) && main_~bit~6 < 256) && 0 <= main_~bit~6;
    assume ((0 <= main_~y~5 && 0 <= main_~i~6) && main_~i~6 < 256) && main_~y~5 < 256;
    main_~y~5 := main_~i~6 + main_~y~5;
    assume main_~c~5 < 256 && 0 <= main_~c~5;
    main_~c~5 := main_~c~5 + 1;
    goto loc1;
  loc3:
    assert false;
}

