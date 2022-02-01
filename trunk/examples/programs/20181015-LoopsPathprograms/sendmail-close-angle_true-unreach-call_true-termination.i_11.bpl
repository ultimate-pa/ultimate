procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#t~nondet1 : int;
    var main_#t~nondet2 : int;
    var main_~inlen~0 : int;
    var main_#t~nondet3 : int;
    var main_#t~post7 : int;
    var main_#t~post6 : int;
    var main_#t~post5 : int;
    var main_#t~post4 : int;
    var main_~buf~0 : int;
    var #in~cond : int;
    var main_#res : int;
    var main_~buflim~0 : int;
    var main_~in~0 : int;
    var main_~bufferlen~0 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet1, main_~buf~0, main_#t~nondet2, main_~inlen~0, main_#t~nondet3, main_~buflim~0, main_~in~0, main_#t~post7, main_~bufferlen~0, main_#t~post6, main_#t~post5, main_#t~post4;
    havoc main_~in~0;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    main_~inlen~0 := main_#t~nondet1;
    havoc main_#t~nondet1;
    assume 0 <= main_#t~nondet2 + 2147483648 && main_#t~nondet2 <= 2147483647;
    main_~bufferlen~0 := main_#t~nondet2;
    havoc main_#t~nondet2;
    havoc main_~buf~0;
    havoc main_~buflim~0;
    assume 1 < main_~bufferlen~0;
    assume 0 < main_~inlen~0;
    assume main_~bufferlen~0 < main_~inlen~0;
    main_~buf~0 := 0;
    main_~in~0 := 0;
    main_~buflim~0 := main_~bufferlen~0 + -2;
    goto loc1;
  loc1:
    assume 0 <= main_#t~nondet3 + 2147483648 && main_#t~nondet3 <= 2147483647;
    assume !(0 == main_#t~nondet3);
    havoc main_#t~nondet3;
    assume !(main_~buflim~0 == main_~buf~0);
    #in~cond := (if 0 <= main_~buf~0 then 1 else 0);
    havoc main_~buf~0;
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

