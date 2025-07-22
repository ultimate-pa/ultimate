procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#t~post10 : int;
    var main_#t~nondet1 : int;
    var main_~bufsize~0 : int;
    var main_#t~nondet2 : int;
    var main_#t~nondet3 : int;
    var main_~i~0 : int;
    var main_#t~post7 : int;
    var main_#t~post6 : int;
    var main_#t~post5 : int;
    var main_#t~post4 : int;
    var main_~len~0 : int;
    var main_~limit~0 : int;
    var main_#t~post9 : int;
    var #in~cond : int;
    var main_#t~post8 : int;
    var main_~j~0 : int;
    var main_#res : int;

  loc0:
    havoc main_#res;
    havoc main_#t~post10, main_#t~nondet1, main_~bufsize~0, main_#t~nondet2, main_#t~nondet3, main_~i~0, main_#t~post7, main_#t~post6, main_#t~post5, main_#t~post4, main_~len~0, main_~limit~0, main_#t~post9, main_#t~post8, main_~j~0;
    havoc main_~len~0;
    havoc main_~i~0;
    havoc main_~j~0;
    havoc main_~bufsize~0;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    main_~bufsize~0 := main_#t~nondet1;
    havoc main_#t~nondet1;
    assume !(main_~bufsize~0 < 0);
    assume 0 <= main_#t~nondet2 + 2147483648 && main_#t~nondet2 <= 2147483647;
    main_~len~0 := main_#t~nondet2;
    havoc main_#t~nondet2;
    main_~limit~0 := main_~bufsize~0 + -4;
    main_~i~0 := 0;
    assume main_~i~0 < main_~len~0;
    main_~j~0 := 0;
    assume main_~i~0 < main_~len~0 && main_~j~0 < main_~limit~0;
    assume main_~i~0 + 1 < main_~len~0;
    #in~cond := (if main_~i~0 + 1 < main_~len~0 then 1 else 0);
    havoc main_~len~0, main_~i~0;
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

