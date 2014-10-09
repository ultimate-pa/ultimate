//
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
            assert 4 + ~q~1!offset <= #length[~q~1!base];
//            call #t~mem1 := read~int(~q~1, 4);
            #t~short2 := #t~mem1 >= 0;
        }
        if (!#t~short2) {
            break;
        } 
        ~q~1 := { base: ~q~1!base, offset: ~q~1!offset + 4 };
    }
    main := 0;
    return;
}

type $Pointer$ = { base : int, offset : int };
var #NULL : { base : int, offset : int };

var #memory_int : [$Pointer$]int;

// procedure read~int(#ptr : $Pointer$, #sizeOfReadType : int) returns (#value : int);    requires #valid[#ptr!base];
//     requires #sizeOfReadType + #ptr!offset <= #length[#ptr!base];
//     ensures #value == #memory_int[#ptr];

var #valid : [int]bool;

var #length : [int]int;

procedure ~malloc(~size : int) returns (#res : $Pointer$);    ensures old(#valid)[#res!base] == false;
    ensures #valid == old(#valid)[#res!base := true];
    ensures #res!offset == 0;
    ensures #res!base != 0;
    ensures #length == old(#length)[#res!base := ~size];
    modifies #valid, #length;

procedure main() returns (main : int);    modifies #valid, #length;


