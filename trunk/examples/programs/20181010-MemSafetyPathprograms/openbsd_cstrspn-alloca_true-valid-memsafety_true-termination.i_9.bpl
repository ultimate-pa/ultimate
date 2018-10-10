var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var read~int_#value : int;
    var cstrspn_~spanp~0.base : int;
    var main_#t~nondet6 : int;
    var cstrspn_#res : int;
    var cstrspn_#t~post4.offset : int;
    var write~int_#ptr.base : int;
    var cstrspn_~s1.offset : int;
    var main_~nondetString1~0.base : int;
    var cstrspn_~spanp~0.offset : int;
    var main_~length2~0 : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var main_#t~malloc9.base : int;
    var cstrspn_#t~post2.offset : int;
    var main_~length1~0 : int;
    var write~int_old_#memory_int : [int][int]int;
    var main_old_#valid : [int]int;
    var main_~nondetString2~0.base : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var cstrspn_~p~0.offset : int;
    var write~int_#sizeOfWrittenType : int;
    var read~int_#ptr.base : int;
    var cstrspn_#in~s1.offset : int;
    var cstrspn_#in~s2.base : int;
    var main_#t~malloc8.offset : int;
    var cstrspn_~sc~0 : int;
    var write~int_#value : int;
    var cstrspn_~s1.base : int;
    var cstrspn_~c~0 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~nondet7 : int;
    var write~int_#ptr.offset : int;
    var cstrspn_#t~mem5 : int;
    var cstrspn_#t~post2.base : int;
    var cstrspn_#t~post4.base : int;
    var main_#t~malloc9.offset : int;
    var cstrspn_~s2.base : int;
    var main_#t~malloc8.base : int;
    var cstrspn_#in~s2.offset : int;
    var cstrspn_~s2.offset : int;
    var #Ultimate.alloc_~size : int;
    var cstrspn_~p~0.base : int;
    var cstrspn_#t~mem3 : int;
    var read~int_#sizeOfReadType : int;
    var main_~nondetString2~0.offset : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_#t~ret10 : int;
    var main_~nondetString1~0.offset : int;
    var cstrspn_#in~s1.base : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~malloc8.base, main_#t~malloc9.base, main_~length1~0, main_#t~nondet6, main_#t~nondet7, main_~nondetString2~0.base, main_~nondetString2~0.offset, main_#t~ret10, main_~nondetString1~0.base, main_#t~malloc8.offset, main_~nondetString1~0.offset, main_#t~malloc9.offset, main_~length2~0;
    assume main_#t~nondet6 <= 2147483647 && 0 <= main_#t~nondet6 + 2147483648;
    main_~length1~0 := main_#t~nondet6;
    havoc main_#t~nondet6;
    assume main_#t~nondet7 <= 2147483647 && 0 <= main_#t~nondet7 + 2147483648;
    main_~length2~0 := main_#t~nondet7;
    havoc main_#t~nondet7;
    assume !(main_~length1~0 < 1);
    assume !(main_~length2~0 < 1);
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := main_~length1~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc8.base, main_#t~malloc8.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~nondetString1~0.base, main_~nondetString1~0.offset := main_#t~malloc8.base, main_#t~malloc8.offset;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := main_~length2~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #length == #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size];
    main_#t~malloc9.base, main_#t~malloc9.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~nondetString2~0.base, main_~nondetString2~0.offset := main_#t~malloc9.base, main_#t~malloc9.offset;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 1, main_~nondetString1~0.base, 0, main_~nondetString1~0.offset + main_~length1~0 + -1;
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    assume 1 == #valid[write~int_#ptr.base];
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    havoc #memory_int;
    assume #memory_int == write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]];
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 1, main_~nondetString2~0.base, 0, main_~length2~0 + main_~nondetString2~0.offset + -1;
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#ptr.offset + write~int_#sizeOfWrittenType <= #length[write~int_#ptr.base];
    assume #valid[write~int_#ptr.base] == 1;
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    havoc #memory_int;
    assume write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]] == #memory_int;
    cstrspn_#in~s2.offset, cstrspn_#in~s1.offset, cstrspn_#in~s2.base, cstrspn_#in~s1.base := main_~nondetString2~0.offset, main_~nondetString1~0.offset, main_~nondetString2~0.base, main_~nondetString1~0.base;
    havoc cstrspn_#res;
    havoc cstrspn_~s1.base, cstrspn_~s2.offset, cstrspn_#t~post2.offset, cstrspn_~p~0.base, cstrspn_~c~0, cstrspn_~spanp~0.base, cstrspn_#t~mem3, cstrspn_#t~post4.offset, cstrspn_~p~0.offset, cstrspn_~s1.offset, cstrspn_#t~mem5, cstrspn_#t~post2.base, cstrspn_#t~post4.base, cstrspn_~sc~0, cstrspn_~spanp~0.offset, cstrspn_~s2.base;
    cstrspn_~s1.base, cstrspn_~s1.offset := cstrspn_#in~s1.base, cstrspn_#in~s1.offset;
    cstrspn_~s2.offset, cstrspn_~s2.base := cstrspn_#in~s2.offset, cstrspn_#in~s2.base;
    cstrspn_~p~0.base, cstrspn_~p~0.offset := cstrspn_~s1.base, cstrspn_~s1.offset;
    havoc cstrspn_~spanp~0.offset, cstrspn_~spanp~0.base;
    havoc cstrspn_~c~0;
    havoc cstrspn_~sc~0;
    goto loc1;
  loc1:
    cstrspn_#t~post2.offset, cstrspn_#t~post2.base := cstrspn_~p~0.offset, cstrspn_~p~0.base;
    cstrspn_~p~0.base, cstrspn_~p~0.offset := cstrspn_#t~post2.base, cstrspn_#t~post2.offset + 1;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := cstrspn_#t~post2.base, cstrspn_#t~post2.offset, 1;
    assume 1 == #valid[read~int_#ptr.base];
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base]) || !(0 <= read~int_#ptr.offset);
    goto loc3;
  loc2_1:
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume 1 == #valid[read~int_#ptr.base];
    assume 0 <= read~int_#ptr.offset && read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base];
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    cstrspn_#t~mem3 := read~int_#value;
    cstrspn_~c~0 := cstrspn_#t~mem3;
    havoc cstrspn_#t~mem3;
    havoc cstrspn_#t~post2.offset, cstrspn_#t~post2.base;
    cstrspn_~spanp~0.offset, cstrspn_~spanp~0.base := cstrspn_~s2.offset, cstrspn_~s2.base;
    cstrspn_#t~post4.base, cstrspn_#t~post4.offset := cstrspn_~spanp~0.base, cstrspn_~spanp~0.offset;
    cstrspn_~spanp~0.offset, cstrspn_~spanp~0.base := cstrspn_#t~post4.offset + 1, cstrspn_#t~post4.base;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := cstrspn_#t~post4.base, cstrspn_#t~post4.offset, 1;
    assume #valid[read~int_#ptr.base] == 1;
    assume 0 <= read~int_#ptr.offset && read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base];
    assume #valid[read~int_#ptr.base] == 1;
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume read~int_#value == #memory_int[read~int_#ptr.base][read~int_#ptr.offset];
    cstrspn_#t~mem5 := read~int_#value;
    cstrspn_~sc~0 := cstrspn_#t~mem5;
    assume !(0 == cstrspn_~sc~0);
    havoc cstrspn_#t~mem5;
    havoc cstrspn_#t~post4.base, cstrspn_#t~post4.offset;
    assume cstrspn_~sc~0 == cstrspn_~c~0;
    goto loc1;
  loc3:
    assert false;
}

