//#rNonTermination
/*
 * Date: 2016-09-10
 * Author: heizmann@informatik.uni-freiburg.de
 */

var #NULL : $Pointer$;

var #valid : [int]int;

var #length : [int]int;

var #memory_int : [$Pointer$]int;

type $Pointer$ = { base : int, offset : int };
procedure ULTIMATE.start() returns ();
modifies #valid, #NULL, #memory_int;
modifies #valid, #length, #memory_int;

implementation ULTIMATE.start() returns (){
    var #t~ret5 : int;
    var main_#res : int;
    var main_#t~malloc0 : $Pointer$;
    var main_#t~malloc1 : $Pointer$;
    var main_#t~mem2 : int;
    var main_#t~mem3 : int;
    var main_#t~post4 : int;
    var main_~x~1 : $Pointer$;
    var main_~y~1 : $Pointer$;
    var #Ultimate.alloc_~size : int, #Ultimate.alloc_#res : $Pointer$;
    var #Ultimate.alloc_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var read~int_#ptr : $Pointer$, read~int_#sizeOfReadType : int, read~int_#value : int;
    var write~int_#value : int, write~int_#ptr : $Pointer$, write~int_#sizeOfWrittenType : int;
    var write~int_old_#memory_int : [$Pointer$]int;

    havoc #Ultimate.alloc_#res;
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res!base] == 0;
    main_#t~malloc0 := #Ultimate.alloc_#res;
    main_~x~1 := main_#t~malloc0;
    #Ultimate.alloc_old_#length, #Ultimate.alloc_old_#valid := #length, #valid;
    while (true)
    {
        read~int_#ptr, read~int_#sizeOfReadType := main_~x~1, 4;
        havoc read~int_#value;
        assume read~int_#value == #memory_int[read~int_#ptr];
        main_#t~mem3 := read~int_#value;
        main_#t~post4 := main_#t~mem3;
        write~int_#value, write~int_#ptr, write~int_#sizeOfWrittenType := main_#t~post4 - 1, main_~x~1, 4;
        havoc #memory_int;
        assume #memory_int == write~int_old_#memory_int[write~int_#ptr := write~int_#value];
    }
}

