procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#t~nondet1 : int;
    var #in~cond : int;
    var main_#res : int;
    var main_#t~nondet2 : int;
    var main_~m~0 : int;
    var main_~n~0 : int;
    var main_~x~0 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet1, main_#t~nondet2, main_~m~0, main_~n~0, main_~x~0;
    main_~x~0 := 0;
    main_~m~0 := 0;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    main_~n~0 := main_#t~nondet1;
    havoc main_#t~nondet1;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~x~0 < main_~n~0);
    assume (0 <= main_~m~0 || (!(main_~n~0 <= 0) && !(0 <= main_~m~0))) || main_~n~0 <= 0;
    #in~cond := (if 0 <= main_~m~0 || main_~n~0 <= 0 then 1 else 0);
    havoc main_~m~0, main_~n~0;
    goto loc3;
  loc2_1:
    assume main_~x~0 < main_~n~0;
    assume 0 <= main_#t~nondet2 + 2147483648 && main_#t~nondet2 <= 2147483647;
    assume !(0 == main_#t~nondet2);
    havoc main_#t~nondet2;
    main_~m~0 := main_~x~0;
    main_~x~0 := main_~x~0 + 1;
    goto loc1;
}

procedure __VERIFIER_assert() returns ()
modifies ;
{
    var #in~cond : int;
    var ~cond : int;

  loc3:
    ~cond := #in~cond;
    assume ~cond == 0;
    goto loc4;
  loc4:
    assert false;
}

