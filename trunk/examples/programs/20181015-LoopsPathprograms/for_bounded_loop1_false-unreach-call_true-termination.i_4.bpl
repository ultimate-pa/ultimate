procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#t~nondet1 : int;
    var #in~cond : int;
    var main_#res : int;
    var main_#t~nondet3 : int;
    var main_~y~0 : int;
    var main_~n~0 : int;
    var main_#t~post2 : int;
    var main_~i~0 : int;
    var main_~x~0 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet1, main_#t~nondet3, main_~y~0, main_~n~0, main_#t~post2, main_~i~0, main_~x~0;
    main_~i~0 := 0;
    main_~x~0 := 0;
    main_~y~0 := 0;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    main_~n~0 := main_#t~nondet1;
    havoc main_#t~nondet1;
    assume 0 < main_~n~0;
    main_~i~0 := 0;
    assume main_~i~0 < main_~n~0;
    main_~x~0 := main_~x~0 + -1 * main_~y~0;
    #in~cond := (if main_~x~0 == 0 then 1 else 0);
    havoc main_~x~0;
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
    assume ~cond == 0;
    goto loc3;
  loc2_1:
    assume !(~cond == 0);
    return;
  loc3:
    assert false;
}

