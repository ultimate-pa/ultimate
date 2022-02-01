 
type bStack = [int][int]bool;
type iStack = [int][int]int;
type iArray = [int]int;
procedure ULTIMATE.start() returns ()
	modifies bStack, iStack, iArray;
{
    var CookiefyRet : bool;
    var intStack : iStack, boolStack : bStack, idStack : iArray, ppStack : iArray, sp : int;
    var foo : bool;

    foo:= false;

  $Ultimate##0:
    call CookiefyRet := enc_havoc_main_T(foo, intStack, boolStack, idStack, ppStack, sp, 0);
    assert CookiefyRet != false;
    return;
}

procedure preturn_T(foao:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int) returns (ret:bool)
	modifies bStack, iStack, iArray;
{
    var func_id : int;
    var foo : bool;
    ret := true;
    foo := false;
  $Ultimate##0:
    func_id := idStack[sp];
    goto $Ultimate##1, $Ultimate##2;
  $Ultimate##1:
    assume func_id == 0;
    call ret := enc_main_T(foo, intStack, boolStack, idStack, ppStack, sp - 1, ppStack[sp]);
    goto $Ultimate##3;
  $Ultimate##2:
    assume !(func_id == 0);
    goto $Ultimate##3;
  $Ultimate##3:
    return;
}

procedure enc_havoc_main_T(fooa:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int, pp:int) returns (ret:bool)
	modifies bStack, iStack, iArray;
{
var foo : bool;
  $Ultimate##0:
        
        foo := false;
    call ret := enc_main_T(foo, intStack, boolStack, idStack, ppStack, sp, pp);
    return;
}

procedure enc_main_T(cookiefy_args_foo:bool, cookiefy_args_intStack:iStack, cookiefy_args_boolStack:bStack, cookiefy_args_idStack:iArray, cookiefy_args_ppStack:iArray, cookiefy_args_sp:int, pp:int) returns (ret:bool)
	modifies bStack, iStack, iArray;
{

    var intStack : iStack, boolStack : bStack, idStack : iArray, ppStack : iArray, sp : int;
    var foo : bool;
    foo:= false;
  $Ultimate##0:
    intStack := cookiefy_args_intStack;
    boolStack := cookiefy_args_boolStack;
    idStack := cookiefy_args_idStack;
    ppStack := cookiefy_args_ppStack;
    sp := cookiefy_args_sp;
    foo := cookiefy_args_foo;
    goto $Ultimate##1, $Ultimate##2;
  $Ultimate##1:
    assume pp == 2;
    goto $Cookiefy##2;
  $Ultimate##2:
    assume !(pp == 2);
    goto $Cookiefy##1;
  $Cookiefy##1:
    goto $Ultimate##3, $Ultimate##4;
  $Ultimate##3:
    ret := true;
    return;
  $Ultimate##4:
    call ret := enc_main_TL(foo, intStack, boolStack, idStack, ppStack, sp, 1);
    goto $Ultimate##5, $Ultimate##6;
  $Ultimate##5:
    assume !ret;
    return;
  $Ultimate##6:
    assume !!ret;
    foo := false;
    goto $Cookiefy##2;
  $Cookiefy##2:
    return;
}

procedure preturn_TL(fodo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int) returns (ret:bool)
	modifies bStack, iStack, iArray;
{
    var func_id : int;
var foo: bool;

    ret:= true;
        foo := false;
  $Ultimate##0:
    func_id := idStack[sp];
    goto $Ultimate##1, $Ultimate##2;
  $Ultimate##1:
    assume func_id == 0;
    call ret := enc_main_TL(foo, intStack, boolStack, idStack, ppStack, sp - 1, ppStack[sp]);
    goto $Ultimate##3;
  $Ultimate##2:
    assume !(func_id == 0);
    goto $Ultimate##3;
  $Ultimate##3:
    return;
}

procedure enc_havoc_main_TL(fooa:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int, pp:int) returns (ret:bool)
	modifies bStack, iStack, iArray;
{
 var foo : bool;
  $Ultimate##0:
       foo := false;
    call ret := enc_main_TL(foo, intStack, boolStack, idStack, ppStack, sp, pp);
    return;
}

procedure enc_main_TL(foo:bool, intStack:iStack, boolStack:bStack, idStack:iArray, ppStack:iArray, sp:int, pp:int) returns (ret:bool)
	modifies bStack, iStack, iArray;
{
  $Ultimate##0:
    ret := !foo;
    return;
}
