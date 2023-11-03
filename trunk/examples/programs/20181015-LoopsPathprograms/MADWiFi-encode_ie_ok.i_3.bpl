procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#t~nondet1 : int;
    var main_~p~0 : int;
    var main_~bufsize~0 : int;
    var #in~cond : int;
    var main_#res : int;
    var main_#t~nondet2 : int;
    var main_~ielen~0 : int;
    var main_#t~nondet3 : int;
    var main_~bufsize_0~0 : int;
    var main_~i~0 : int;
    var main_~leader_len~0 : int;
    var main_#t~post4 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet1, main_~p~0, main_~bufsize~0, main_#t~nondet2, main_~ielen~0, main_#t~nondet3, main_~bufsize_0~0, main_~i~0, main_~leader_len~0, main_#t~post4;
    havoc main_~p~0;
    havoc main_~i~0;
    havoc main_~leader_len~0;
    havoc main_~bufsize~0;
    havoc main_~bufsize_0~0;
    havoc main_~ielen~0;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    main_~leader_len~0 := main_#t~nondet1;
    havoc main_#t~nondet1;
    assume 0 <= main_#t~nondet2 + 2147483648 && main_#t~nondet2 <= 2147483647;
    main_~bufsize~0 := main_#t~nondet2;
    havoc main_#t~nondet2;
    assume 0 <= main_#t~nondet3 + 2147483648 && main_#t~nondet3 <= 2147483647;
    main_~ielen~0 := main_#t~nondet3;
    havoc main_#t~nondet3;
    assume main_~leader_len~0 < 1000000;
    assume main_~bufsize~0 < 1000000;
    assume main_~ielen~0 < 1000000;
    assume 0 < main_~leader_len~0;
    assume 0 < main_~bufsize~0;
    assume 0 < main_~ielen~0;
    assume !(main_~bufsize~0 < main_~leader_len~0);
    main_~p~0 := 0;
    main_~bufsize_0~0 := main_~bufsize~0;
    main_~bufsize~0 := main_~bufsize~0 + -1 * main_~leader_len~0;
    main_~p~0 := main_~p~0 + main_~leader_len~0;
    assume !(main_~bufsize~0 < 2 * main_~ielen~0);
    main_~i~0 := 0;
    goto loc1;
  loc1:
    assume main_~i~0 < main_~ielen~0 && 2 < main_~bufsize~0;
    #in~cond := (if 0 <= main_~p~0 then 1 else 0);
    havoc main_~p~0;
    goto loc2;
}

procedure __VERIFIER_assert() returns ()
modifies ;
{
    var #in~cond : int;
    var ~cond : int;

  loc2:
    ~cond := #in~cond;
    goto loc3;
  loc3:
    goto loc3_0, loc3_1;
  loc3_0:
    assume ~cond == 0;
    goto loc4;
  loc3_1:
    assume !(~cond == 0);
    return;
  loc4:
    assert false;
}

