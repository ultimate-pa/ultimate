var ~last~0 : int;

procedure ULTIMATE.start() returns ()
modifies ~last~0;
{
    var main_~st~0 : int;
    var nondet_~x~0 : int;
    var main_~a~0 : int;
    var main_#t~ret0 : int;
    var __VERIFIER_assert_~cond : int;
    var main_#res : int;
    var main_~c~0 : int;
    var main_#t~post1 : int;
    var nondet_#res : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~b~0 : int;

  loc0:
    ~last~0 := 0;
    havoc main_#res;
    havoc main_~st~0, main_~a~0, main_#t~ret0, main_~c~0, main_#t~post1, main_~b~0;
    havoc nondet_#res;
    havoc nondet_~x~0;
    havoc nondet_~x~0;
    nondet_#res := nondet_~x~0;
    main_#t~ret0 := nondet_#res;
    assume 0 <= main_#t~ret0 + 2147483648 && main_#t~ret0 <= 2147483647;
    ~last~0 := main_#t~ret0;
    havoc main_#t~ret0;
    main_~a~0 := 0;
    main_~b~0 := 0;
    main_~c~0 := 0;
    main_~st~0 := 0;
    main_~st~0 := 1;
    main_~c~0 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~c~0 < 200000);
    assume !(0 == main_~st~0) || !(~last~0 + 1 == main_~c~0);
    main_~a~0 := main_~a~0 + 2;
    main_~b~0 := main_~b~0 + 2;
    assume !(0 == main_~st~0) || !(~last~0 == main_~c~0);
    assume (!(main_~a~0 == main_~b~0) || (main_~a~0 == main_~b~0 && 200000 == main_~c~0)) || !(200000 == main_~c~0);
    __VERIFIER_assert_#in~cond := (if main_~c~0 == 200000 && main_~b~0 == main_~a~0 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume 0 == __VERIFIER_assert_~cond;
    goto loc3;
  loc2_1:
    assume main_~c~0 < 200000;
    assume !(~last~0 == main_~c~0);
    main_#t~post1 := main_~c~0;
    main_~c~0 := main_#t~post1 + 1;
    havoc main_#t~post1;
    goto loc1;
  loc3:
    assert false;
}

