// #Safe
/* 
 * Reproducible with (non-interprocedural) forward predicates.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-01-01
 *
 */

implementation ULTIMATE.start() returns (){
    var arr.base : int, arr.offset : int;
    var p.base : int, p.offset : int;
    var i : int;

    call arr.base, arr.offset := ldv_malloc(true);
    i := 0;
    assume !(arr.base == 0 && arr.offset == 0);
    call p.base, p.offset := ldv_malloc(true);
    call write~$Pointer$(p.base, p.offset, arr.base, arr.offset + i, 4);
    i := i + 1;
    call p.base, p.offset := ldv_malloc(true);
    call write~$Pointer$(p.base, p.offset, arr.base, arr.offset + i, 4);
    return;
}

procedure ldv_malloc(size : bool) returns (res.base : int, res.offset : int)
modifies #valid, #length;
{
        call res.base, res.offset := #Ultimate.alloc((if size then 39 else -17));
}




var #valid : [int]int;

var #length : [int]int;

var #memory_$Pointer$.base : [int,int]int, #memory_$Pointer$.offset : [int,int]int;

procedure write~$Pointer$(#value.base : int, #value.offset : int, #ptr.base : int, #ptr.offset : int, #sizeOfWrittenType : int) returns ();
requires #sizeOfWrittenType + #ptr.offset <= #length[#ptr.base] && 0 <= #ptr.offset;
modifies #memory_$Pointer$.base, #memory_$Pointer$.offset;

procedure #Ultimate.alloc(size : int) returns (res.base : int, res.offset : int);
free ensures old(#valid)[res.base] == 0;
free ensures #valid == old(#valid)[res.base := 1];
free ensures res.offset == 0;
free ensures res.base != 0;
free ensures #length == old(#length)[res.base := size];
modifies #valid, #length;


procedure ULTIMATE.start() returns ();
modifies #valid;
modifies #valid, #length, #memory_$Pointer$.base, #memory_$Pointer$.offset;

