///////////////////////////////////////////////
// RESULT: Ultimate proved your program to be incorrect!
///////////////////////////////////////////////
type bStack = [int][int]bool;
type iStack = [int][int]int;
type iArray = [int]int;
procedure main() returns ()
{
    var CookiefyRet : bool;
    var intStack : iStack, boolStack : bStack, idStack : iArray, ppStack : iArray, sp : int;
    var foo : bool;

    foo := true;
    call CookiefyRet := enc_havoc_main_T(foo, intStack, boolStack, idStack, ppStack, sp, 0);
    assert CookiefyRet != false;
}

procedure preturn_T(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int) returns (ret:bool)
{
    var func_id : int;

    func_id := idStack[sp];
    if (func_id == 0) {
        call ret := enc_main_T(foo, intStack, boolStack, idStack, ppStack, sp - 1, ppStack[sp]);
    }
}

procedure enc_havoc_main_T(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int, pp:int) returns (ret:bool)
{
    call ret := enc_main_T(foo, intStack, boolStack, idStack, ppStack, sp, pp);
}

procedure enc_main_T(cookiefy_args_foo:bool, cookiefy_args_intStack:iStack, cookiefy_args_boolStack:bStack, cookiefy_args_idStack:iArray, cookiefy_args_ppStack:iArray, cookiefy_args_sp:int, pp:int) returns (ret:bool)
{
    var intStack : iStack, boolStack : bStack, idStack : iArray, ppStack : iArray, sp : int;
    var foo : bool;

    intStack := cookiefy_args_intStack;
    boolStack := cookiefy_args_boolStack;
    idStack := cookiefy_args_idStack;
    ppStack := cookiefy_args_ppStack;
    sp := cookiefy_args_sp;
    foo := cookiefy_args_foo;
    if (pp == 2) {
        goto $Cookiefy##2;
    }
  $Cookiefy##1:
    if (*) {
        ret := true;
        return;
    }
    call ret := enc_main_TL(foo, intStack, boolStack, idStack, ppStack, sp, 2);
    if (!ret) {
        return;
    }
	$Cookiefy##2:																	//TODO: correct labels and jumps in clals
    foo := true;
	if (*) {
        ret := true;
        return;
    }
    call ret := enc_main_TL(foo, intStack, boolStack, idStack, ppStack, sp, 3);
    if (!ret) {
        return;
    }
	$Cookiefy##3:
    return;
}

procedure preturn_TL(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int) returns (ret:bool)
{
    var func_id : int;

    func_id := idStack[sp];
    if (func_id == 0) {
        call ret := enc_main_TL(foo, intStack, boolStack, idStack, ppStack, sp - 1, ppStack[sp]);
    }
}

procedure enc_havoc_main_TL(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int, pp:int) returns (ret:bool)
{
    call ret := enc_main_TL(foo, intStack, boolStack, idStack, ppStack, sp, pp);
}

procedure enc_main_TL(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int, pp:int) returns (ret:bool)
{
    ret := !foo;
    return;
}
