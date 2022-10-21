procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#t~nondet0 : int;
    var main_~len~0 : int;
    var main_~a~0 : [int]int;
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_#t~post1 : int;
    var main_~i~0 : int;
    var __VERIFIER_assert_#in~cond : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet0, main_~len~0, main_~a~0, main_#t~post1, main_~i~0;
    havoc main_~a~0;
    main_~len~0 := 0;
    havoc main_~i~0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume 0 == main_#t~nondet0 % 256;
    havoc main_#t~nondet0;
    assume (!(main_~len~0 % 4294967296 < 5) || !(0 <= main_~len~0 % 4294967296)) || (0 <= main_~len~0 % 4294967296 && main_~len~0 % 4294967296 < 5);
    __VERIFIER_assert_#in~cond := (if 0 <= main_~len~0 % 4294967296 && main_~len~0 % 4294967296 < 5 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume 0 == __VERIFIER_assert_~cond;
    goto loc3;
  loc2_1:
    assume !(main_#t~nondet0 % 256 == 0);
    havoc main_#t~nondet0;
    assume !(4 == main_~len~0 % 4294967296);
    main_~a~0 := main_~a~0[(if main_~len~0 % 4294967296 <= 2147483647 then main_~len~0 % 4294967296 else main_~len~0 % 4294967296 + -4294967296) := 0];
    main_#t~post1 := main_~len~0;
    main_~len~0 := main_#t~post1 + 1;
    havoc main_#t~post1;
    goto loc1;
  loc3:
    assert false;
}

