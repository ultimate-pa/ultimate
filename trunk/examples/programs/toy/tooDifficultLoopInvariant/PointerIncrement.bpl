implementation main() returns (main : int){
    var #t~malloc0 : $Pointer$;
    var #t~post3 : $Pointer$;
    var #t~mem1 : int;
    var #t~short2 : bool;
    var ~p~1 : $Pointer$;
    var ~q~1 : $Pointer$;

    call #t~malloc0 := ~malloc(400);
    ~p~1 := #t~malloc0;
    ~q~1 := ~p~1;
    while (true)
    {
        #t~short2 := ~q~1!offset < { base: ~p~1!base, offset: ~p~1!offset + 400 }!offset;
        if (#t~short2) {
            call #t~mem1 := read~int(~q~1, 4);
            #t~short2 := #t~mem1 >= 0;
        }
      Loop~0:
        if (!#t~short2) {
            havoc #t~mem1;
            havoc #t~short2;
            break;
        } else {
            havoc #t~mem1;
            havoc #t~short2;
        }
        #t~post3 := ~q~1;
        ~q~1 := { base: #t~post3!base, offset: #t~post3!offset + 4 };
        havoc #t~post3;
    }
    main := 0;
    return;
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

procedure write~int(#value : int, #ptr : $Pointer$, #sizeOfWrittenType : int) returns ();    requires #valid[#ptr!base];
    requires #sizeOfWrittenType + #ptr!offset <= #length[#ptr!base];
    modifies #memory_int;
    ensures #memory_int == old(#memory_int)[#ptr := #value];

procedure read~int(#ptr : $Pointer$, #sizeOfReadType : int) returns (#value : int);    requires #valid[#ptr!base];
    requires #sizeOfReadType + #ptr!offset <= #length[#ptr!base];
    ensures #value == #memory_int[#ptr];

var #valid : [int]bool;

var #length : [int]int;

procedure ~free(~addr : $Pointer$) returns ();    requires ~addr!offset == 0;
    requires #valid[~addr!base];
    ensures #valid == old(#valid)[~addr!base := false];
    modifies #valid;

procedure ~malloc(~size : int) returns (#res : $Pointer$);    ensures old(#valid)[#res!base] == false;
    ensures #valid == old(#valid)[#res!base := true];
    ensures #res!offset == 0;
    ensures #res!base != 0;
    ensures #length == old(#length)[#res!base := ~size];
    modifies #valid, #length;

const #sizeof~INT : int;
axiom #sizeof~INT == 4;
procedure main() returns (main : int);    modifies #valid, #length;

procedure ULTIMATE.init() returns ();    modifies #valid, #NULL;
    modifies ;

procedure ULTIMATE.start() returns ();    modifies #valid, #NULL;
    modifies #valid, #length;

