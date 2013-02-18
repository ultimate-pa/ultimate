
type bStack = [int][int]bool;
type iStack = [int][int]int;
type iArray = [int]int;
var retVal_int : int;
procedure main() returns ()
modifies retVal_int;
{
    var CookiefyRet : bool;
    var intStack : iStack, boolStack : bStack, idStack : iArray, ppStack : iArray, sp : int;
    var foo : bool;

    havoc foo;
    call CookiefyRet := enc_havoc_main_T(foo, intStack, boolStack, idStack, ppStack, sp, 0);
    assert CookiefyRet != false;
}

procedure preturn_T(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int) returns (ret:bool)
modifies retVal_int;
{
    var func_id : int;

    func_id := idStack[sp];
    if (func_id == 0) {
        call ret := enc_main_T(intStack[sp][0], foo, intStack, boolStack, idStack, ppStack, sp - 1, ppStack[sp]);
    }
    if (func_id == 1) {
        call ret := enc_recursive_T(intStack[sp][0], intStack[sp][1], foo, intStack, boolStack, idStack, ppStack, sp - 1, ppStack[sp]);
    }
}

procedure enc_havoc_main_T(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int, pp:int) returns (ret:bool)
{
    var bla : int;

    havoc bla;
    call ret := enc_main_T(bla, foo, intStack, boolStack, idStack, ppStack, sp, pp);
}

procedure enc_main_T(cookiefy_args_bla:int, cookiefy_args_foo:bool, cookiefy_args_intStack:iStack, cookiefy_args_boolStack:bStack, cookiefy_args_idStack:iArray, cookiefy_args_ppStack:iArray, cookiefy_args_sp:int, pp:int) returns (ret:bool)
modifies retVal_int;
{
    var bla : int;
    var intStack : iStack, boolStack : bStack, idStack : iArray, ppStack : iArray, sp : int;
    var foo : bool;

    bla := cookiefy_args_bla;
    intStack := cookiefy_args_intStack;
    boolStack := cookiefy_args_boolStack;
    idStack := cookiefy_args_idStack;
    ppStack := cookiefy_args_ppStack;
    sp := cookiefy_args_sp;
    foo := cookiefy_args_foo;
    if (pp == 4) {
        goto $Cookiefy##4;
    }
    if (pp == 3) {
        goto $Cookiefy##3;
    }
    if (pp == 2) {
        goto $Cookiefy##2;
    }
  $Cookiefy##1:
    intStack[sp][0] := bla;
    ppStack[sp] := 2;
    idStack[sp] := 0;
    call ret := enc_havoc_recursive_T(0, foo, intStack, boolStack, idStack, ppStack, sp + 1, 0);
  $Cookiefy##2:
    bla := retVal_int;
  $Cookiefy##3:
    return;
  $Cookiefy##4:
}

procedure enc_havoc_recursive_T(cookiefy_args_i:int, foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int, pp:int) returns (ret:bool)
modifies retVal_int;
{
    var i : int;
    var v : int;

    havoc i;
    havoc v;
    i := cookiefy_args_i;
    call ret := enc_recursive_T(i, v, foo, intStack, boolStack, idStack, ppStack, sp, pp);
}

procedure enc_recursive_T(cookiefy_args_i:int, cookiefy_args_v:int, cookiefy_args_foo:bool, cookiefy_args_intStack:iStack, cookiefy_args_boolStack:bStack, cookiefy_args_idStack:iArray, cookiefy_args_ppStack:iArray, cookiefy_args_sp:int, pp:int) returns (ret:bool)
    modifies retVal_int;
{
    var i : int;
    var v : int;
    var intStack : iStack, boolStack : bStack, idStack : iArray, ppStack : iArray, sp : int;
    var foo : bool;

    i := cookiefy_args_i;
    v := cookiefy_args_v;
    intStack := cookiefy_args_intStack;
    boolStack := cookiefy_args_boolStack;
    idStack := cookiefy_args_idStack;
    ppStack := cookiefy_args_ppStack;
    sp := cookiefy_args_sp;
    foo := cookiefy_args_foo;
    if (pp == 14) {
        goto $Cookiefy##14;
    }
    if (pp == 13) {
        goto $Cookiefy##13;
    }
    if (pp == 12) {
        goto $Cookiefy##12;
    }
    if (pp == 11) {
        goto $Cookiefy##11;
    }
    if (pp == 10) {
        goto $Cookiefy##10;
    }
    if (pp == 9) {
        goto $Cookiefy##9;
    }
    if (pp == 8) {
        goto $Cookiefy##8;
    }
    if (pp == 7) {
        goto $Cookiefy##7;
    }
    if (pp == 6) {
        goto $Cookiefy##6;
    }
    if (pp == 5) {
        goto $Cookiefy##5;
    }
    if (pp == 4) {
        goto $Cookiefy##4;
    }
    if (pp == 3) {
        goto $Cookiefy##3;
    }
    if (pp == 2) {
        goto $Cookiefy##2;
    }
    if (*) {
        ret := true;
        return;
    }
    call ret := enc_recursive_TL(i, v, foo, intStack, boolStack, idStack, ppStack, sp, 1);
    if (!ret) {
        return;
    }
  $Cookiefy##1:
    goto lif, lelse;
  lelse:
    if (*) {
        ret := true;
        return;
    }
    call ret := enc_recursive_TL(i, v, foo, intStack, boolStack, idStack, ppStack, sp, 2);
    if (!ret) {
        return;
    }
  $Cookiefy##2:
    assume i == 102;
  $Cookiefy##3:
    intStack[sp][0] := i;
    intStack[sp][1] := v;
    ppStack[sp] := 4;
    idStack[sp] := 1;
    call ret := enc_havoc_recursive_T(i + 1, foo, intStack, boolStack, idStack, ppStack, sp + 1, 0);
  $Cookiefy##4:
    v := retVal_int;
    if (*) {
        ret := true;
        return;
    }
    call ret := enc_recursive_TL(i, v, foo, intStack, boolStack, idStack, ppStack, sp, 5);
    if (!ret) {
        return;
    }
  $Cookiefy##5:
    foo := true;
  $Cookiefy##6:
    if (*) {
        ret := true;
        return;
    }
    call ret := enc_recursive_TL(i, v, foo, intStack, boolStack, idStack, ppStack, sp, 7);
    if (!ret) {
        return;
    }
    retVal_int := v;
    call ret := preturn_T(foo, intStack, boolStack, idStack, ppStack, sp);
    return;
  lif:
    if (*) {
        ret := true;
        return;
    }
    call ret := enc_recursive_TL(i, v, foo, intStack, boolStack, idStack, ppStack, sp, 7);
    if (!ret) {
        return;
    }
  $Cookiefy##7:
    assume i < 100;
  $Cookiefy##8:
    intStack[sp][0] := i;
    intStack[sp][1] := v;
    ppStack[sp] := 9;
    idStack[sp] := 1;
    call ret := enc_havoc_recursive_T(i + 1, foo, intStack, boolStack, idStack, ppStack, sp + 1, 0);
  $Cookiefy##9:
    v := retVal_int;
    if (*) {
        ret := true;
        return;
    }
    call ret := enc_recursive_TL(i, v, foo, intStack, boolStack, idStack, ppStack, sp, 10);
    if (!ret) {
        return;
    }
  $Cookiefy##10:
    foo := false;
  $Cookiefy##11:
    if (*) {
        ret := true;
        return;
    }
    call ret := enc_recursive_TL(i, v, foo, intStack, boolStack, idStack, ppStack, sp, 12);
    if (!ret) {
        return;
    }
    retVal_int := v;
    call ret := preturn_T(foo, intStack, boolStack, idStack, ppStack, sp);
    return;
    if (*) {
        ret := true;
        return;
    }
    call ret := enc_recursive_TL(i, v, foo, intStack, boolStack, idStack, ppStack, sp, 12);
    if (!ret) {
        return;
    }
  $Cookiefy##12:
    v := 1;
  $Cookiefy##13:
    if (*) {
        ret := true;
        return;
    }
    call ret := enc_recursive_TL(i, v, foo, intStack, boolStack, idStack, ppStack, sp, 14);
    if (!ret) {
        return;
    }
    retVal_int := v;
    call ret := preturn_T(foo, intStack, boolStack, idStack, ppStack, sp);
    return;
  $Cookiefy##14:
}

procedure preturn_TL(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int) returns (ret:bool)
modifies retVal_int;
{
    var func_id : int;

    func_id := idStack[sp];
    if (func_id == 0) {
        call ret := enc_main_TL(intStack[sp][0], foo, intStack, boolStack, idStack, ppStack, sp - 1, ppStack[sp]);
    }
    if (func_id == 1) {
        call ret := enc_recursive_TL(intStack[sp][0], intStack[sp][1], foo, intStack, boolStack, idStack, ppStack, sp - 1, ppStack[sp]);
    }
}

procedure enc_havoc_main_TL(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int, pp:int) returns (ret:bool)
modifies retVal_int;
{
    var bla : int;

    havoc bla;
    call ret := enc_main_TL(bla, foo, intStack, boolStack, idStack, ppStack, sp, pp);
}

procedure enc_main_TL(bla:int, foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int, pp:int) returns (ret:bool)
modifies retVal_int;
{
    ret := !foo;
    return;
}

procedure enc_havoc_recursive_TL(cookiefy_args_i:int, foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int, pp:int) returns (ret:bool)
{
    var i : int;
    var v : int;

    havoc i;
    havoc v;
    i := cookiefy_args_i;
    call ret := enc_recursive_TL(i, v, foo, intStack, boolStack, idStack, ppStack, sp, pp);
}

procedure enc_recursive_TL(i:int, v:int, foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int, pp:int) returns (ret:bool)
    modifies retVal_int;
{
    ret := !foo;
    return;
}
