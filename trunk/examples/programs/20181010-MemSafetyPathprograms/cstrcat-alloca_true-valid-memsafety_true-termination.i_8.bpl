var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var cstrcat_#t~post4.offset : int;
    var read~int_#value : int;
    var main_#t~malloc11.offset : int;
    var main_#t~nondet8 : int;
    var cstrcat_#t~post5.base : int;
    var main_#t~malloc11.base : int;
    var main_~length3~0 : int;
    var write~int_#ptr.base : int;
    var cstrcat_#t~post3.base : int;
    var cstrcat_#t~post4.base : int;
    var main_~nondetString1~0.base : int;
    var cstrcat_#in~s1.offset : int;
    var main_~length2~0 : int;
    var #Ultimate.alloc_#res.base : int;
    var cstrcat_#in~s2.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var cstrcat_~s1.base : int;
    var main_#t~ret12.offset : int;
    var main_~length1~0 : int;
    var write~int_old_#memory_int : [int][int]int;
    var main_old_#valid : [int]int;
    var main_~nondetString2~0.base : int;
    var cstrcat_#t~post5.offset : int;
    var cstrcat_~s2.offset : int;
    var main_#t~ret12.base : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var cstrcat_~s~0.base : int;
    var write~int_#sizeOfWrittenType : int;
    var read~int_#ptr.base : int;
    var cstrcat_~s1.offset : int;
    var write~int_#value : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~nondet9 : int;
    var main_#t~nondet7 : int;
    var cstrcat_#in~s2.offset : int;
    var write~int_#ptr.offset : int;
    var cstrcat_#res.base : int;
    var cstrcat_~s~0.offset : int;
    var main_#t~malloc10.offset : int;
    var cstrcat_#in~s1.base : int;
    var #Ultimate.alloc_~size : int;
    var read~int_#sizeOfReadType : int;
    var main_~nondetString2~0.offset : int;
    var cstrcat_#res.offset : int;
    var main_#t~malloc10.base : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_~nondetString1~0.offset : int;
    var cstrcat_#t~post3.offset : int;
    var cstrcat_~s2.base : int;
    var cstrcat_#t~mem2 : int;
    var cstrcat_#t~mem6 : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~malloc11.offset, main_#t~nondet8, main_#t~nondet9, main_#t~ret12.offset, main_~length1~0, main_#t~malloc11.base, main_#t~nondet7, main_~nondetString2~0.base, main_~nondetString2~0.offset, main_#t~ret12.base, main_~length3~0, main_#t~malloc10.base, main_~nondetString1~0.base, main_~nondetString1~0.offset, main_~length2~0, main_#t~malloc10.offset;
    assume main_#t~nondet7 <= 2147483647 && 0 <= main_#t~nondet7 + 2147483648;
    main_~length1~0 := main_#t~nondet7;
    havoc main_#t~nondet7;
    assume 0 <= main_#t~nondet8 + 2147483648 && main_#t~nondet8 <= 2147483647;
    main_~length2~0 := main_#t~nondet8;
    havoc main_#t~nondet8;
    assume 0 <= main_#t~nondet9 + 2147483648 && main_#t~nondet9 <= 2147483647;
    main_~length3~0 := main_#t~nondet9;
    havoc main_#t~nondet9;
    assume !(main_~length1~0 < 1);
    assume !(main_~length2~0 < 2);
    assume !(main_~length3~0 < 1);
    assume !(main_~length2~0 < main_~length1~0 + main_~length3~0) && !(main_~length2~0 < main_~length3~0);
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := main_~length1~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc10.base, main_#t~malloc10.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~nondetString1~0.base, main_~nondetString1~0.offset := main_#t~malloc10.base, main_#t~malloc10.offset;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := main_~length2~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #length == #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size];
    main_#t~malloc11.offset, main_#t~malloc11.base := #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    main_~nondetString2~0.base, main_~nondetString2~0.offset := main_#t~malloc11.base, main_#t~malloc11.offset;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 1, main_~nondetString1~0.base, 0, main_~nondetString1~0.offset + main_~length1~0 + -1;
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    assume 1 == #valid[write~int_#ptr.base];
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    havoc #memory_int;
    assume #memory_int == write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]];
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 1, main_~nondetString2~0.base, 0, main_~length3~0 + main_~nondetString2~0.offset + -1;
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#ptr.offset + write~int_#sizeOfWrittenType <= #length[write~int_#ptr.base];
    assume #valid[write~int_#ptr.base] == 1;
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    havoc #memory_int;
    assume write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]] == #memory_int;
    cstrcat_#in~s2.base, cstrcat_#in~s1.base, cstrcat_#in~s1.offset, cstrcat_#in~s2.offset := main_~nondetString1~0.base, main_~nondetString2~0.base, main_~nondetString2~0.offset, main_~nondetString1~0.offset;
    havoc cstrcat_#res.offset, cstrcat_#res.base;
    havoc cstrcat_#t~post4.offset, cstrcat_~s1.base, cstrcat_#t~post5.base, cstrcat_#t~post5.offset, cstrcat_~s2.offset, cstrcat_~s~0.base, cstrcat_#t~post3.base, cstrcat_#t~post4.base, cstrcat_~s1.offset, cstrcat_#t~post3.offset, cstrcat_~s2.base, cstrcat_#t~mem2, cstrcat_~s~0.offset, cstrcat_#t~mem6;
    cstrcat_~s1.offset, cstrcat_~s1.base := cstrcat_#in~s1.offset, cstrcat_#in~s1.base;
    cstrcat_~s2.base, cstrcat_~s2.offset := cstrcat_#in~s2.base, cstrcat_#in~s2.offset;
    cstrcat_~s~0.base, cstrcat_~s~0.offset := cstrcat_~s1.base, cstrcat_~s1.offset;
    goto loc1;
  loc1:
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := cstrcat_~s~0.base, cstrcat_~s~0.offset, 1;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(1 == #valid[read~int_#ptr.base]);
    goto loc3;
  loc2_1:
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume 1 == #valid[read~int_#ptr.base];
    assume 0 <= read~int_#ptr.offset && read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base];
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    cstrcat_#t~mem2 := read~int_#value;
    assume !(0 == cstrcat_#t~mem2);
    havoc cstrcat_#t~mem2;
    cstrcat_#t~post3.base, cstrcat_#t~post3.offset := cstrcat_~s~0.base, cstrcat_~s~0.offset;
    cstrcat_~s~0.base, cstrcat_~s~0.offset := cstrcat_#t~post3.base, cstrcat_#t~post3.offset + 1;
    havoc cstrcat_#t~post3.base, cstrcat_#t~post3.offset;
    goto loc1;
  loc3:
    assert false;
}

