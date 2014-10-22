implementation main() returns (main : int){
    var #t~post2 : int;
    var #t~mem1 : int;
    var #t~mem3 : int;
    var ~#a~4 : $Pointer$;
    var ~p1~4 : $Pointer$;

    call ~#a~4 := ~malloc(4);
    havoc ~p1~4;
    ~p1~4 := ~#a~4;
    call write~int(5, ~#a~4, 4);
    call #t~mem1 := read~int(~#a~4, 4);
    #t~post2 := #t~mem1;
    call write~int(#t~post2 - 1, ~#a~4, 4);
    havoc #t~post2;
    havoc #t~mem1;
    call #t~mem3 := read~int(~p1~4, 4);
    if (#t~mem3 == 4) {
        havoc #t~mem3;
        call assert_fail();
        goto ERROR;
    } else {
        havoc #t~mem3;
    }
    main := 0;
    call ~free(~#a~4);
    havoc ~#a~4;
    return;
  ERROR:
    if (*) {
        assert false;
    }
    main := 1;
    call ~free(~#a~4);
    havoc ~#a~4;
    return;
    call ~free(~#a~4);
    havoc ~#a~4;
}

implementation ULTIMATE.init() returns (){
    #NULL := { base: 0, offset: 0 };
    #valid[0] := false;
}

implementation ULTIMATE.start() returns (){
    var #t~ret4 : int;

    call ULTIMATE.init();
    call #t~ret4 := main();
}

type $Pointer$ = { base : int, offset : int };
var #NULL : { base : int, offset : int };

var #memory_int : [$Pointer$]int;

procedure write~int(#value : int, #ptr : $Pointer$, #sizeOfWrittenType : int) returns ();
free requires #valid[#ptr!base];

free requires #sizeOfWrittenType + #ptr!offset <= #length[#ptr!base];

modifies #memory_int;

ensures #memory_int == old(#memory_int)[#ptr := #value];

procedure read~int(#ptr : $Pointer$, #sizeOfReadType : int) returns (#value : int);
free requires #valid[#ptr!base];

free requires #sizeOfReadType + #ptr!offset <= #length[#ptr!base];

ensures #value == #memory_int[#ptr];

var #valid : [int]bool;

var #length : [int]int;

procedure ~free(~addr : $Pointer$) returns ();
procedure ~malloc(~size : int) returns (#res : $Pointer$);
ensures old(#valid)[#res!base] == false;

ensures #valid == old(#valid)[#res!base := true];

ensures #res!offset == 0;

ensures #res!base != 0;

ensures #length == old(#length)[#res!base := ~size];

modifies #valid, #length;

const #sizeof~INT : int;
axiom #sizeof~INT == 4;
procedure __VERIFIER_error() returns ();
modifies ;

procedure printf(#in~format : $Pointer$) returns ();
modifies ;

procedure assert_fail() returns ();
modifies ;

procedure main() returns (main : int);
modifies #valid, #length, #memory_int;

procedure ULTIMATE.init() returns ();
modifies #valid, #NULL;

modifies ;

procedure ULTIMATE.start() returns ();
modifies #valid, #NULL, #memory_int;

modifies #valid, #length, #memory_int;

