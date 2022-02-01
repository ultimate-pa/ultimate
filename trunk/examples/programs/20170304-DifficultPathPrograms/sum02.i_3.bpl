implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~nondet0 : int;
    var main_#t~post1 : int;
    var main_~i~6 : int;
    var main_~n~6 : int;
    var main_~sn~6 : int;
    var main_~nl~6 : int;
    var main_~gauss~6 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet0, main_#t~post1, main_~i~6, main_~n~6, main_~sn~6, main_~nl~6, main_~gauss~6;
    havoc main_~i~6;
    main_~n~6 := main_#t~nondet0;
    havoc main_#t~nondet0;
    main_~sn~6 := 0;
    assume main_~n~6 % 4294967296 % 18446744073709551616 < 4294967296;
    main_~i~6 := 0;
    goto loc1;
  loc1:
    assume true;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~i~6 % 4294967296 <= main_~n~6 % 4294967296);
    main_~nl~6 := main_~n~6 % 4294967296;
    main_~gauss~6 := (if main_~nl~6 * (main_~nl~6 + 1) % 18446744073709551616 < 0 && main_~nl~6 * (main_~nl~6 + 1) % 18446744073709551616 % 2 != 0 then main_~nl~6 * (main_~nl~6 + 1) % 18446744073709551616 / 2 + 1 else main_~nl~6 * (main_~nl~6 + 1) % 18446744073709551616 / 2);
    __VERIFIER_assert_#in~cond := (if main_~sn~6 % 18446744073709551616 == main_~gauss~6 % 18446744073709551616 || main_~sn~6 % 18446744073709551616 == 0 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc3;
  loc2_1:
    assume !!(main_~i~6 % 4294967296 <= main_~n~6 % 4294967296);
    main_~sn~6 := main_~sn~6 + main_~i~6 % 4294967296;
    main_#t~post1 := main_~i~6;
    main_~i~6 := main_#t~post1 + 1;
    havoc main_#t~post1;
    goto loc1;
  loc3:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

