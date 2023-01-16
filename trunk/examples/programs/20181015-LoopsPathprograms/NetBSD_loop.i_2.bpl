procedure ULTIMATE.start() returns ()
modifies ;
{
    var main_#t~nondet1 : int;
    var main_~bound_off~0 : int;
    var main_~glob2_p_off~0 : int;
    var #in~cond : int;
    var main_~MAXPATHLEN~0 : int;
    var main_~pathbuf_off~0 : int;
    var main_#res : int;
    var main_~glob2_pathbuf_off~0 : int;
    var main_#t~post2 : int;
    var main_~glob2_pathlim_off~0 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~nondet1, main_~bound_off~0, main_~glob2_p_off~0, main_~MAXPATHLEN~0, main_~pathbuf_off~0, main_~glob2_pathbuf_off~0, main_#t~post2, main_~glob2_pathlim_off~0;
    havoc main_~MAXPATHLEN~0;
    havoc main_~pathbuf_off~0;
    havoc main_~bound_off~0;
    havoc main_~glob2_p_off~0;
    havoc main_~glob2_pathbuf_off~0;
    havoc main_~glob2_pathlim_off~0;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    main_~MAXPATHLEN~0 := main_#t~nondet1;
    havoc main_#t~nondet1;
    assume 0 < main_~MAXPATHLEN~0 && main_~MAXPATHLEN~0 < 2147483647;
    main_~pathbuf_off~0 := 0;
    main_~bound_off~0 := main_~MAXPATHLEN~0 + main_~pathbuf_off~0;
    main_~glob2_pathbuf_off~0 := main_~pathbuf_off~0;
    main_~glob2_pathlim_off~0 := main_~bound_off~0;
    main_~glob2_p_off~0 := main_~glob2_pathbuf_off~0;
    assume main_~glob2_p_off~0 <= main_~glob2_pathlim_off~0;
    #in~cond := (if 0 <= main_~glob2_p_off~0 then 1 else 0);
    havoc main_~glob2_p_off~0;
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

