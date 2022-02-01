//
implementation main() returns (main : int){
    var #t~malloc0 : $Pointer$;
    var #t~post3 : $Pointer$;
    var #t~mem1 : int;
    var #t~short2 : bool;
    var p : $Pointer$;
    var q : $Pointer$;

    call p := ~malloc(400);
    q := p;
    while (true)
    {
        if (q!offset < p!offset + 400) {
            assert 4 + q!offset <= #length[q!base];

        } else {
            break;
        } 
        q := { base: q!base, offset: q!offset + 4 };
    }
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


