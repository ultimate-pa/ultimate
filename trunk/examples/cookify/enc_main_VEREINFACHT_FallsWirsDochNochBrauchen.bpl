procedure enc_main_T(cookiefy_args_t:int, cookiefy_args_tn:int, cookiefy_args_mad:bool, cookiefy_args_warn:bool, cookiefy_args_intStack:iStack, cookiefy_args_boolStack:bStack, cookiefy_args_idStack:iArray, cookiefy_args_ppStack:iArray, cookiefy_args_sp:int, pp:int) returns (ret:bool)
{
    var t, tn : int;
    var intStack : iStack, boolStack : bStack, idStack : iArray, ppStack : iArray, sp : int;
    var mad : bool, warn : bool;

    t := cookiefy_args_t;
    tn := cookiefy_args_tn;
    intStack := cookiefy_args_intStack;
    boolStack := cookiefy_args_boolStack;
    idStack := cookiefy_args_idStack;
    ppStack := cookiefy_args_ppStack;
    sp := cookiefy_args_sp;
    mad := cookiefy_args_mad;
    warn := cookiefy_args_warn;
    if (pp == 13) {
        goto $Cookiefy##13;
    }
    ...
    if (pp == 4) {
        goto $Cookiefy##13;
    }
  $Ultimate##1:
    goto $Ultimate##2, $Ultimate##4;
  $Ultimate##2:
    assume true;
    havoc tn;
  $Cookiefy##4:
    intStack[sp][0] := t;
    intStack[sp][1] := tn;
    ppStack[sp] := 5;
    idStack[sp] := 0;
    call ret := enc_havoc_calcTemp_T(tn, mad, warn, intStack, boolStack, idStack, ppStack, sp + 1, 0);
  $Cookiefy##5:
    t := retVal_int;
    goto $Ultimate##4, $Ultimate##5;

  $Ultimate##4:
    assume t > 13;
  $Cookiefy##8:
    intStack[sp][0] := t;
    intStack[sp][1] := tn;
    ppStack[sp] := 9;
    idStack[sp] := 0;
    call ret := enc_havoc_warn_T(mad, warn, intStack, boolStack, idStack, ppStack, sp + 1, 0);
  $Cookiefy##9:
    goto $Ultimate##6;

  $Ultimate##5:
    assume !(t > 13);
  $Cookiefy##12:
    intStack[sp][0] := t;
    intStack[sp][1] := tn;
    ppStack[sp] := 13;
    idStack[sp] := 0;
    call ret := enc_havoc_unwarn_T(mad, warn, intStack, boolStack, idStack, ppStack, sp + 1, 0);
  $Cookiefy##13:
    goto $Ultimate##6;

  $Ultimate##6:
    goto $Ultimate##1;
    assume !true;
    return;
}
