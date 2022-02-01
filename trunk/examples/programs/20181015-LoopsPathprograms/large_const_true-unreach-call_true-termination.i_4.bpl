procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_~k~0 : int;
    var main_#t~nondet1 : int;
    var main_~argv.offset : int;
    var __VERIFIER_assert_~cond : int;
    var main_#t~nondet3 : int;
    var main_#t~post2 : int;
    var main_~c1~0 : int;
    var #in~argv.offset : int;
    var main_#t~post5 : int;
    var main_#t~post4 : int;
    var main_~argv.base : int;
    var main_~c2~0 : int;
    var main_~j~0 : int;
    var main_~argc : int;
    var #in~argc : int;
    var #in~argv.base : int;
    var main_#in~argv.base : int;
    var main_~c3~0 : int;
    var main_#in~argv.offset : int;
    var main_~n~0 : int;
    var main_~i~0 : int;
    var main_~v~0 : int;
    var main_#res : int;
    var main_#in~argc : int;
    var __VERIFIER_assert_#in~cond : int;

  loc0:
    main_#in~argv.base, main_#in~argv.offset, main_#in~argc := #in~argv.base, #in~argv.offset, #in~argc;
    havoc main_#res;
    havoc main_~c3~0, main_~k~0, main_#t~nondet1, main_~argv.offset, main_#t~nondet3, main_~n~0, main_#t~post2, main_~c1~0, main_~i~0, main_#t~post5, main_#t~post4, main_~argv.base, main_~v~0, main_~c2~0, main_~j~0, main_~argc;
    main_~argc := main_#in~argc;
    main_~argv.base, main_~argv.offset := main_#in~argv.base, main_#in~argv.offset;
    main_~c1~0 := 4000;
    main_~c2~0 := 2000;
    main_~c3~0 := 10000;
    havoc main_~n~0;
    havoc main_~v~0;
    havoc main_~i~0;
    havoc main_~k~0;
    havoc main_~j~0;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    main_~n~0 := main_#t~nondet1;
    havoc main_#t~nondet1;
    assume main_~n~0 < 10 && 0 <= main_~n~0;
    main_~k~0 := 0;
    main_~i~0 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~i~0 < main_~n~0);
    main_~j~0 := 0;
    assume main_~j~0 < main_~n~0;
    __VERIFIER_assert_#in~cond := (if 0 < main_~k~0 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume 0 == __VERIFIER_assert_~cond;
    goto loc3;
  loc2_1:
    assume main_~i~0 < main_~n~0;
    main_#t~post2 := main_~i~0;
    main_~i~0 := main_#t~post2 + 1;
    havoc main_#t~post2;
    assume 0 <= main_#t~nondet3 + 2147483648 && main_#t~nondet3 <= 2147483647;
    main_~v~0 := main_#t~nondet3;
    havoc main_#t~nondet3;
    assume 0 <= main_~v~0 && main_~n~0 < 2;
    assume !(0 == main_~v~0);
    assume 1 == main_~v~0;
    main_~k~0 := main_~c2~0 + main_~k~0;
    goto loc1;
  loc3:
    assert false;
}

