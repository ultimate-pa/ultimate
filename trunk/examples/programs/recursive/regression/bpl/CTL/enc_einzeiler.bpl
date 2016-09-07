//#Safe 
type bStack = [int][int]bool;
type iStack = [int][int]int;
type iArray = [int]int;
procedure main() returns ()
{
    var CookiefyRet : bool;
    var intStack : iStack, boolStack : bStack, idStack : iArray, ppStack : iArray, sp : int;
    var foo : bool;

    foo:= false;

  Label0:
    call CookiefyRet := enc_havoc_main_T(foo, intStack, boolStack, idStack, ppStack, sp, 0);
    assert CookiefyRet != false;
    return;
}

procedure preturn_T(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int) returns (ret:bool)
{
    var func_id : int;
    ret := true;

  Label0:
    func_id := idStack[sp];
    goto Label1, Label2;
  Label1:
    assume func_id == 0;
    call ret := enc_main_T(foo, intStack, boolStack, idStack, ppStack, sp - 1, ppStack[sp]);
    goto Label3;
  Label2:
    assume !(func_id == 0);
    goto Label3;
  Label3:
    return;
}

procedure enc_havoc_main_T(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int, pp:int) returns (ret:bool)
{

  Label0:
    call ret := enc_main_T(foo, intStack, boolStack, idStack, ppStack, sp, pp);
    return;
}

procedure enc_main_T(cookiefy_args_foo:bool, cookiefy_args_intStack:iStack, cookiefy_args_boolStack:bStack, cookiefy_args_idStack:iArray, cookiefy_args_ppStack:iArray, cookiefy_args_sp:int, pp:int) returns (ret:bool)
{

    var intStack : iStack, boolStack : bStack, idStack : iArray, ppStack : iArray, sp : int;
    var foo : bool;
  Label0:
    intStack := cookiefy_args_intStack;
    boolStack := cookiefy_args_boolStack;
    idStack := cookiefy_args_idStack;
    ppStack := cookiefy_args_ppStack;
    sp := cookiefy_args_sp;
    foo := cookiefy_args_foo;
    goto Label1, Label2;
  Label1:
    assume pp == 2;
    goto $Cookiefy##2;
  Label2:
    assume !(pp == 2);
    goto $Cookiefy##1;
  $Cookiefy##1:
    goto Label3, Label4;
  Label3:
    ret := true;
    return;
  Label4:
    call ret := enc_main_TL(foo, intStack, boolStack, idStack, ppStack, sp, 1);
    goto Label5, Label6;
  Label5:
    assume !ret;
    return;
  Label6:
    assume !!ret;
    foo := false;
    goto $Cookiefy##2;
  $Cookiefy##2:
    return;
}

procedure preturn_TL(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int) returns (ret:bool)
{
    var func_id : int;
    ret:= true;
  Label0:
    func_id := idStack[sp];
    goto Label1, Label2;
  Label1:
    assume func_id == 0;
    call ret := enc_main_TL(foo, intStack, boolStack, idStack, ppStack, sp - 1, ppStack[sp]);
    goto Label3;
  Label2:
    assume !(func_id == 0);
    goto Label3;
  Label3:
    return;
}

procedure enc_havoc_main_TL(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int, pp:int) returns (ret:bool)
{
  Label0:
    call ret := enc_main_TL(foo, intStack, boolStack, idStack, ppStack, sp, pp);
    return;
}

procedure enc_main_TL(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int, pp:int) returns (ret:bool)
{
  Label0:
    ret := !foo;
    return;
}