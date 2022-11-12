procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_~k~0 : int;
    var main_~j~0 : int;
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_~i~0 : int;
    var __VERIFIER_assert_#in~cond : int;

  loc0:
    havoc main_#res;
    havoc main_~k~0, main_~j~0, main_~i~0;
    main_~i~0 := 0;
    main_~j~0 := 0;
    main_~k~0 := 0;
    goto loc1;
  loc1:
    assume main_~k~0 % 4294967296 < 268435455;
    main_~i~0 := main_~i~0 + 1;
    main_~j~0 := main_~j~0 + 2;
    main_~k~0 := main_~k~0 + 3;
    assume (!(2 * main_~i~0 % 4294967296 == main_~j~0 % 4294967296) || !(3 * main_~i~0 % 4294967296 == main_~k~0 % 4294967296)) || (3 * main_~i~0 % 4294967296 == main_~k~0 % 4294967296 && 2 * main_~i~0 % 4294967296 == main_~j~0 % 4294967296);
    __VERIFIER_assert_#in~cond := (if main_~j~0 % 4294967296 == 2 * main_~i~0 % 4294967296 && main_~k~0 % 4294967296 == 3 * main_~i~0 % 4294967296 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(0 == __VERIFIER_assert_~cond);
    goto loc1;
  loc2_1:
    assume 0 == __VERIFIER_assert_~cond;
    goto loc3;
  loc3:
    assert false;
}

