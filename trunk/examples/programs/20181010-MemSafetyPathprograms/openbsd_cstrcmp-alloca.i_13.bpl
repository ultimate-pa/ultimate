var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var cstrcmp_#t~mem9 : int;
    var read~int_#value : int;
    var cstrcmp_#in~s2.offset : int;
    var main_#t~nondet11 : int;
    var main_#t~malloc13.base : int;
    var main_#t~malloc12.base : int;
    var cstrcmp_#t~mem3 : int;
    var cstrcmp_~s1.offset : int;
    var write~int_#ptr.base : int;
    var cstrcmp_~s1.base : int;
    var main_~nondetString1~0.base : int;
    var cstrcmp_~s2.base : int;
    var main_~length2~0 : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var cstrcmp_#t~post5.offset : int;
    var main_~length1~0 : int;
    var write~int_old_#memory_int : [int][int]int;
    var main_old_#valid : [int]int;
    var main_~nondetString2~0.base : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var main_#t~malloc12.offset : int;
    var cstrcmp_#res : int;
    var write~int_#sizeOfWrittenType : int;
    var read~int_#ptr.base : int;
    var cstrcmp_#in~s1.offset : int;
    var write~int_#value : int;
    var cstrcmp_#in~s1.base : int;
    var cstrcmp_#t~mem8 : int;
    var main_#t~nondet10 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var cstrcmp_#t~post5.base : int;
    var cstrcmp_#t~mem4 : int;
    var write~int_#ptr.offset : int;
    var cstrcmp_#t~mem6 : int;
    var #Ultimate.alloc_~size : int;
    var cstrcmp_~s2.offset : int;
    var main_#t~malloc13.offset : int;
    var cstrcmp_#t~post2.offset : int;
    var read~int_#sizeOfReadType : int;
    var main_~nondetString2~0.offset : int;
    var cstrcmp_#t~post2.base : int;
    var cstrcmp_#t~pre7.base : int;
    var cstrcmp_#t~pre7.offset : int;
    var main_#t~ret14 : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_~nondetString1~0.offset : int;
    var cstrcmp_#in~s2.base : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~nondet10, main_#t~nondet11, main_#t~malloc13.base, main_#t~malloc13.offset, main_#t~malloc12.base, main_~length1~0, main_~nondetString2~0.base, main_~nondetString2~0.offset, main_#t~malloc12.offset, main_#t~ret14, main_~nondetString1~0.base, main_~nondetString1~0.offset, main_~length2~0;
    assume 0 <= main_#t~nondet10 + 2147483648 && main_#t~nondet10 <= 2147483647;
    main_~length1~0 := main_#t~nondet10;
    havoc main_#t~nondet10;
    assume 0 <= main_#t~nondet11 + 2147483648 && main_#t~nondet11 <= 2147483647;
    main_~length2~0 := main_#t~nondet11;
    havoc main_#t~nondet11;
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
    main_#t~malloc12.offset, main_#t~malloc12.base := #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    main_~nondetString1~0.base, main_~nondetString1~0.offset := main_#t~malloc12.base, main_#t~malloc12.offset;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := main_~length2~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #length == #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size];
    main_#t~malloc13.base, main_#t~malloc13.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~nondetString2~0.base, main_~nondetString2~0.offset := main_#t~malloc13.base, main_#t~malloc13.offset;
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
    cstrcmp_#in~s2.offset, cstrcmp_#in~s1.offset, cstrcmp_#in~s1.base, cstrcmp_#in~s2.base := main_~nondetString2~0.offset, main_~nondetString1~0.offset, main_~nondetString1~0.base, main_~nondetString2~0.base;
    havoc cstrcmp_#res;
    havoc cstrcmp_#t~mem9, cstrcmp_#t~mem8, cstrcmp_~s2.offset, cstrcmp_#t~post5.offset, cstrcmp_#t~post2.offset, cstrcmp_#t~post5.base, cstrcmp_#t~mem3, cstrcmp_~s1.offset, cstrcmp_#t~mem4, cstrcmp_#t~mem6, cstrcmp_#t~post2.base, cstrcmp_#t~pre7.base, cstrcmp_#t~pre7.offset, cstrcmp_~s1.base, cstrcmp_~s2.base;
    cstrcmp_~s1.base, cstrcmp_~s1.offset := cstrcmp_#in~s1.base, cstrcmp_#in~s1.offset;
    cstrcmp_~s2.offset, cstrcmp_~s2.base := cstrcmp_#in~s2.offset, cstrcmp_#in~s2.base;
    goto loc1;
  loc1:
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := cstrcmp_~s1.base, cstrcmp_~s1.offset, 1;
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
    cstrcmp_#t~mem3 := read~int_#value;
    cstrcmp_#t~post2.base, cstrcmp_#t~post2.offset := cstrcmp_~s2.base, cstrcmp_~s2.offset;
    cstrcmp_~s2.offset, cstrcmp_~s2.base := cstrcmp_#t~post2.offset + 1, cstrcmp_#t~post2.base;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := cstrcmp_#t~post2.base, cstrcmp_#t~post2.offset, 1;
    assume #valid[read~int_#ptr.base] == 1;
    assume 0 <= read~int_#ptr.offset && read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base];
    assume #valid[read~int_#ptr.base] == 1;
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume read~int_#value == #memory_int[read~int_#ptr.base][read~int_#ptr.offset];
    cstrcmp_#t~mem4 := read~int_#value;
    assume cstrcmp_#t~mem4 == cstrcmp_#t~mem3;
    havoc cstrcmp_#t~mem4;
    havoc cstrcmp_#t~mem3;
    havoc cstrcmp_#t~post2.base, cstrcmp_#t~post2.offset;
    cstrcmp_#t~post5.offset, cstrcmp_#t~post5.base := cstrcmp_~s1.offset, cstrcmp_~s1.base;
    cstrcmp_~s1.base, cstrcmp_~s1.offset := cstrcmp_#t~post5.base, cstrcmp_#t~post5.offset + 1;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := cstrcmp_#t~post5.base, cstrcmp_#t~post5.offset, 1;
    assume 1 == #valid[read~int_#ptr.base];
    assume 0 <= read~int_#ptr.offset && read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base];
    assume #valid[read~int_#ptr.base] == 1;
    assume 0 <= read~int_#ptr.offset && read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base];
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    cstrcmp_#t~mem6 := read~int_#value;
    assume !(0 == cstrcmp_#t~mem6);
    havoc cstrcmp_#t~post5.offset, cstrcmp_#t~post5.base;
    havoc cstrcmp_#t~mem6;
    goto loc1;
  loc3:
    assert false;
}

