procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#in~argv.base : int;
    var main_#t~nondet1 : int;
    var main_#in~argv.offset : int;
    var main_~argv.offset : int;
    var main_#t~nondet4 : int;
    var main_#t~nondet5 : int;
    var main_#t~post3 : int;
    var main_~n~0 : int;
    var main_#t~post2 : int;
    var main_~i~0 : int;
    var main_#t~post7 : int;
    var main_~r~0 : int;
    var #in~argv.offset : int;
    var main_#t~post6 : int;
    var main_~argv.base : int;
    var #in~cond : int;
    var main_~j~0 : int;
    var main_#res : int;
    var main_~l~0 : int;
    var main_#in~argc : int;
    var main_~argc : int;
    var #in~argc : int;
    var #in~argv.base : int;

  loc0:
    main_#in~argv.base, main_#in~argv.offset, main_#in~argc := #in~argv.base, #in~argv.offset, #in~argc;
    havoc main_#res;
    havoc main_#t~nondet1, main_~argv.offset, main_#t~nondet4, main_#t~nondet5, main_#t~post3, main_~n~0, main_#t~post2, main_~i~0, main_#t~post7, main_~r~0, main_#t~post6, main_~argv.base, main_~j~0, main_~l~0, main_~argc;
    main_~argc := main_#in~argc;
    main_~argv.base, main_~argv.offset := main_#in~argv.base, main_#in~argv.offset;
    havoc main_~n~0;
    havoc main_~l~0;
    havoc main_~r~0;
    havoc main_~i~0;
    havoc main_~j~0;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    main_~n~0 := main_#t~nondet1;
    havoc main_#t~nondet1;
    assume 1 <= main_~n~0 && main_~n~0 <= 1000000;
    assume (main_~n~0 % 2 == 0 || (!(main_~n~0 % 2 == 0) && main_~n~0 < 0)) || !(main_~n~0 < 0);
    main_~l~0 := (if !(main_~n~0 % 2 == 0) && main_~n~0 < 0 then main_~n~0 / 2 + 1 else main_~n~0 / 2) + 1;
    main_~r~0 := main_~n~0;
    assume 1 < main_~l~0;
    main_#t~post2 := main_~l~0;
    main_~l~0 := main_#t~post2 + -1;
    havoc main_#t~post2;
    assume 1 < main_~r~0;
    main_~i~0 := main_~l~0;
    main_~j~0 := 2 * main_~l~0;
    assume main_~j~0 <= main_~r~0;
    assume !(main_~j~0 < main_~r~0);
    #in~cond := (if 1 <= main_~j~0 then 1 else 0);
    havoc main_~j~0;
    goto loc1;
}

procedure __VERIFIER_assert() returns ()
modifies ;
{
    var #in~cond : int;
    var ~cond : int;

  loc1:
    ~cond := #in~cond;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(~cond == 0);
    return;
  loc2_1:
    assume ~cond == 0;
    goto loc3;
  loc3:
    assert false;
}

