procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#t~nondet1 : int;
    var #in~cond : int;
    var main_~j~0 : int;
    var main_#res : int;
    var main_~nlen~0 : int;
    var main_#t~post3 : int;
    var main_~offset~0 : int;
    var main_#t~post2 : int;
    var main_~i~0 : int;
    var main_~length~0 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet1, main_~j~0, main_~nlen~0, main_#t~post3, main_~offset~0, main_#t~post2, main_~i~0, main_~length~0;
    havoc main_~offset~0;
    havoc main_~length~0;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    main_~nlen~0 := main_#t~nondet1;
    havoc main_#t~nondet1;
    havoc main_~i~0;
    havoc main_~j~0;
    main_~i~0 := 0;
    goto loc1;
  loc1:
    assume main_~i~0 < main_~nlen~0;
    main_~j~0 := 0;
    goto loc2;
  loc2:
    goto loc3;
  loc3:
    goto loc3_0, loc3_1;
  loc3_0:
    assume !(main_~j~0 < 8);
    main_#t~post2 := main_~i~0;
    main_~i~0 := main_#t~post2 + 1;
    havoc main_#t~post2;
    goto loc1;
  loc3_1:
    assume main_~j~0 < 8;
    #in~cond := (if main_~i~0 + 1 <= main_~nlen~0 then 1 else 0);
    havoc main_~nlen~0, main_~i~0;
    goto loc4;
}

procedure __VERIFIER_assert() returns ()
modifies ;
{
    var #in~cond : int;
    var ~cond : int;

  loc4:
    ~cond := #in~cond;
    goto loc5;
  loc5:
    goto loc5_0, loc5_1;
  loc5_0:
    assume ~cond == 0;
    goto loc6;
  loc5_1:
    assume !(~cond == 0);
    return;
  loc6:
    assert false;
}

