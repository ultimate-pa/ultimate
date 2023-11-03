var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var cstrcspn_#t~post2.base : int;
    var read~int_#value : int;
    var main_#t~nondet6 : int;
    var cstrcspn_#t~post4.base : int;
    var cstrcspn_~s1.offset : int;
    var write~int_#ptr.base : int;
    var main_~nondetString1~0.base : int;
    var main_~length2~0 : int;
    var #Ultimate.alloc_#res.base : int;
    var cstrcspn_~sc~0 : int;
    var #Ultimate.alloc_#res.offset : int;
    var main_#t~malloc9.base : int;
    var main_~length1~0 : int;
    var cstrcspn_~s2.base : int;
    var write~int_old_#memory_int : [int][int]int;
    var main_old_#valid : [int]int;
    var main_~nondetString2~0.base : int;
    var cstrcspn_#t~post2.offset : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var cstrcspn_~p~0.base : int;
    var write~int_#sizeOfWrittenType : int;
    var read~int_#ptr.base : int;
    var main_#t~malloc8.offset : int;
    var write~int_#value : int;
    var cstrcspn_~c~0 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~nondet7 : int;
    var write~int_#ptr.offset : int;
    var cstrcspn_~s2.offset : int;
    var cstrcspn_#in~s1.base : int;
    var cstrcspn_#in~s2.base : int;
    var cstrcspn_#in~s1.offset : int;
    var main_#t~malloc9.offset : int;
    var main_#t~malloc8.base : int;
    var #Ultimate.alloc_~size : int;
    var cstrcspn_#t~mem5 : int;
    var cstrcspn_~spanp~0.offset : int;
    var cstrcspn_~s1.base : int;
    var read~int_#sizeOfReadType : int;
    var cstrcspn_~spanp~0.base : int;
    var main_~nondetString2~0.offset : int;
    var cstrcspn_#t~mem3 : int;
    var cstrcspn_~p~0.offset : int;
    var cstrcspn_#in~s2.offset : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_#t~ret10 : int;
    var main_~nondetString1~0.offset : int;
    var cstrcspn_#res : int;
    var cstrcspn_#t~post4.offset : int;

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
    cstrcspn_#in~s2.offset, cstrcspn_#in~s1.base, cstrcspn_#in~s2.base, cstrcspn_#in~s1.offset := main_~nondetString2~0.offset, main_~nondetString1~0.base, main_~nondetString2~0.base, main_~nondetString1~0.offset;
    havoc cstrcspn_#res;
    havoc cstrcspn_#t~post2.base, cstrcspn_#t~mem5, cstrcspn_~spanp~0.offset, cstrcspn_~s1.base, cstrcspn_~s2.base, cstrcspn_#t~post4.base, cstrcspn_~s1.offset, cstrcspn_~spanp~0.base, cstrcspn_#t~post2.offset, cstrcspn_#t~mem3, cstrcspn_~p~0.offset, cstrcspn_~p~0.base, cstrcspn_~s2.offset, cstrcspn_~c~0, cstrcspn_#t~post4.offset, cstrcspn_~sc~0;
    cstrcspn_~s1.base, cstrcspn_~s1.offset := cstrcspn_#in~s1.base, cstrcspn_#in~s1.offset;
    cstrcspn_~s2.offset, cstrcspn_~s2.base := cstrcspn_#in~s2.offset, cstrcspn_#in~s2.base;
    havoc cstrcspn_~p~0.base, cstrcspn_~p~0.offset;
    havoc cstrcspn_~spanp~0.offset, cstrcspn_~spanp~0.base;
    havoc cstrcspn_~c~0;
    havoc cstrcspn_~sc~0;
    cstrcspn_~p~0.base, cstrcspn_~p~0.offset := cstrcspn_~s1.base, cstrcspn_~s1.offset;
    cstrcspn_#t~post2.base, cstrcspn_#t~post2.offset := cstrcspn_~p~0.base, cstrcspn_~p~0.offset;
    cstrcspn_~p~0.base, cstrcspn_~p~0.offset := cstrcspn_#t~post2.base, cstrcspn_#t~post2.offset + 1;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := cstrcspn_#t~post2.base, cstrcspn_#t~post2.offset, 1;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume 1 == #valid[read~int_#ptr.base];
    assume 0 <= read~int_#ptr.offset && read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base];
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    cstrcspn_#t~mem3 := read~int_#value;
    cstrcspn_~c~0 := cstrcspn_#t~mem3;
    havoc cstrcspn_#t~post2.base, cstrcspn_#t~post2.offset;
    havoc cstrcspn_#t~mem3;
    cstrcspn_~spanp~0.offset, cstrcspn_~spanp~0.base := cstrcspn_~s2.offset, cstrcspn_~s2.base;
    goto loc1;
  loc1:
    cstrcspn_#t~post4.base, cstrcspn_#t~post4.offset := cstrcspn_~spanp~0.base, cstrcspn_~spanp~0.offset;
    cstrcspn_~spanp~0.offset, cstrcspn_~spanp~0.base := cstrcspn_#t~post4.offset + 1, cstrcspn_#t~post4.base;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := cstrcspn_#t~post4.base, cstrcspn_#t~post4.offset, 1;
    assume #valid[read~int_#ptr.base] == 1;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(0 <= read~int_#ptr.offset) || !(read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base]);
    goto loc3;
  loc2_1:
    assume 0 <= read~int_#ptr.offset && read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base];
    assume #valid[read~int_#ptr.base] == 1;
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume read~int_#value == #memory_int[read~int_#ptr.base][read~int_#ptr.offset];
    cstrcspn_#t~mem5 := read~int_#value;
    cstrcspn_~sc~0 := cstrcspn_#t~mem5;
    assume !(cstrcspn_~sc~0 == cstrcspn_~c~0);
    havoc cstrcspn_#t~post4.base, cstrcspn_#t~post4.offset;
    havoc cstrcspn_#t~mem5;
    assume !(cstrcspn_~sc~0 == 0);
    goto loc1;
  loc3:
    assert false;
}

