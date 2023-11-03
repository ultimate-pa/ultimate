procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#t~post10 : int;
    var main_#t~nondet1 : int;
    var main_#t~nondet3 : int;
    var main_#t~nondet9 : int;
    var main_#t~nondet6 : int;
    var main_#t~nondet7 : int;
    var main_#t~post5 : int;
    var main_~t~0 : int;
    var main_#t~post4 : int;
    var main_~tagbuf_len~0 : int;
    var #in~cond : int;
    var main_#t~post8 : int;
    var main_#res : int;
    var main_#t~pre2 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~post10, main_#t~nondet1, main_~tagbuf_len~0, main_#t~post8, main_#t~nondet3, main_#t~pre2, main_#t~nondet9, main_#t~nondet6, main_#t~nondet7, main_#t~post5, main_~t~0, main_#t~post4;
    havoc main_~tagbuf_len~0;
    havoc main_~t~0;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    main_~tagbuf_len~0 := main_#t~nondet1;
    havoc main_#t~nondet1;
    assume 1 <= main_~tagbuf_len~0;
    main_~t~0 := 0;
    main_#t~pre2 := main_~tagbuf_len~0 + -1;
    main_~tagbuf_len~0 := main_~tagbuf_len~0 + -1;
    havoc main_#t~pre2;
    assume !(main_~tagbuf_len~0 == main_~t~0);
    assume 0 <= main_#t~nondet3 + 2147483648 && main_#t~nondet3 <= 2147483647;
    assume !(0 == main_#t~nondet3);
    havoc main_#t~nondet3;
    #in~cond := (if 0 <= main_~t~0 then 1 else 0);
    havoc main_~t~0;
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

