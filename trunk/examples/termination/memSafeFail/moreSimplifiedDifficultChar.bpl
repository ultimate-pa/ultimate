//
implementation cstrcpy(#in~s1 : $Pointer$, #in~s2 : $Pointer$) returns ()
{
    var ~s1 : $Pointer$;
    var ~s2 : $Pointer$;
    var #t~mem1 : int;
    var #t~mem2 : int;
    var #t~post3 : $Pointer$;

    ~s1 := #in~s1;
    ~s2 := #in~s2;
    while (true)
    {
      Loop~0:
        call #t~mem1 := read~int(~s2, 1);
        call write~int(#t~mem1, ~s1, 1);
        havoc #t~mem1;
        call #t~mem2 := read~int(~s1, 1);
        if (#t~mem2 == 0) {
            havoc #t~mem2;
            break;
        } else {
            havoc #t~mem2;
        }
        #t~post3 := ~s2;
        ~s2 := { base: #t~post3!base, offset: #t~post3!offset + 1 };
        havoc #t~post3;
    }
}



implementation ULTIMATE.start() returns ()
{
    var length : int;
    var string : $Pointer$;

    assume (length >=1);
	assume ourLength == length;
	assume string!offset == 0;
	assume #memory_int[{ base: string!base, offset: string!offset + (length - 1) * 1 }] == 0;
    call cstrcpy(string, string);
}

type $Pointer$ = { base : int, offset : int };
var #memory_int : [$Pointer$]int;
procedure write~int(#value : int, #ptr : $Pointer$, #sizeOfWrittenType : int) returns ();
//    requires #valid[#ptr!base];
//    requires #sizeOfWrittenType + #ptr!offset <= #length[#ptr!base];
    modifies #memory_int;
    ensures #memory_int == old(#memory_int)[#ptr := #value];

procedure read~int(#ptr : $Pointer$, #sizeOfReadType : int) returns (#value : int);
//    requires #valid[#ptr!base];
    requires #sizeOfReadType + #ptr!offset <= ourLength;
    ensures #value == #memory_int[#ptr];

var #valid : [int]bool;
var #length : [int]int;
var ourLength : int;

procedure __VERIFIER_nondet_int() returns (#res : int);
    modifies ;

procedure cstrcpy(#in~s1 : $Pointer$, #in~s2 : $Pointer$) returns ();
    modifies #memory_int;


procedure ULTIMATE.start() returns ();
    modifies #valid, #memory_int;
    modifies #memory_int, #valid, #length;

