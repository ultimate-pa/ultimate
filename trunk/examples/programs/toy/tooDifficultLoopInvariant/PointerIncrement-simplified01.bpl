implementation main() returns (main : int){
    var p : $Pointer$;
    var q : $Pointer$;
    var #t~mem1 : int;
    var #t~short2 : bool;

    call p := ~malloc(24);
    q := p;
    while (true)
    {
//        assert ( (q!offset - p!offset) % 4 == 0 && q!offset % 4 == 0 && p!offset % 4 == 0 && q!offset <= p!offset + 24 &&
//                p!offset == 0 && p!offset >=0 && q!offset >= p!offset && #length[q!base] == 24 && #length[p!base] == 24);
//        assert ( q!offset == p!offset || q!offset == p!offset + 4 || q!offset == p!offset + 8 || q!offset == p!offset + 12 || q!offset == p!offset + 16 || q!offset == p!offset + 20 || q!offset == p!offset + 24);
//         #t~short2 := q!offset < { base: p!base, offset: p!offset + 24 }!offset;
//        if (q!offset < { base: p!base, offset: p!offset + 24 }!offset) {
        if (q!offset < 24) {
            assert (4 + q!offset <= 24);
//            call #t~mem1 := read~int(q, 4);
        } else {
            break;
        }
        //assert (q!offset + 4 <= #length[q!base]);
        q := { base: q!base, offset: q!offset + 4 };
        //assert (q!offset <= #length[q!base] && (q!offset - p!offset) % 4 == 0);
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

const #sizeof~INT : int;
axiom #sizeof~INT == 4;
procedure main() returns (main : int);    modifies #valid, #length;


