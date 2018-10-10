var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var cstrncat_#t~post3.offset : int;
    var read~int_#value : int;
    var main_#t~nondet11 : int;
    var cstrncat_~n : int;
    var main_#t~malloc13.base : int;
    var main_#t~malloc14.base : int;
    var cstrncat_~s1.base : int;
    var cstrncat_~s2.base : int;
    var write~int_#ptr.base : int;
    var cstrncat_#t~mem2 : int;
    var main_~nondetString1~0.base : int;
    var cstrncat_~s~0.offset : int;
    var main_~length2~0 : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var cstrncat_#t~short6 : bool;
    var main_~n~0 : int;
    var main_~length1~0 : int;
    var write~int_old_#memory_int : [int][int]int;
    var cstrncat_~s~0.base : int;
    var main_old_#valid : [int]int;
    var main_~nondetString2~0.base : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var cstrncat_#t~post8.base : int;
    var write~int_#sizeOfWrittenType : int;
    var cstrncat_#res.offset : int;
    var read~int_#ptr.base : int;
    var cstrncat_#t~post7 : int;
    var write~int_#value : int;
    var cstrncat_#t~post4.base : int;
    var cstrncat_~s1.offset : int;
    var main_#t~nondet10 : int;
    var main_#t~nondet12 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var write~int_#ptr.offset : int;
    var main_#t~ret15.base : int;
    var cstrncat_#t~mem9 : int;
    var cstrncat_#in~n : int;
    var cstrncat_#t~mem5 : int;
    var cstrncat_~s2.offset : int;
    var cstrncat_#in~s1.base : int;
    var cstrncat_#in~s2.base : int;
    var #Ultimate.alloc_~size : int;
    var main_#t~malloc13.offset : int;
    var main_#t~ret15.offset : int;
    var cstrncat_#t~post4.offset : int;
    var read~int_#sizeOfReadType : int;
    var cstrncat_#in~s1.offset : int;
    var cstrncat_#t~post8.offset : int;
    var main_~nondetString2~0.offset : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var cstrncat_#res.base : int;
    var main_~nondetString1~0.offset : int;
    var cstrncat_#in~s2.offset : int;
    var cstrncat_#t~post3.base : int;
    var main_#t~malloc14.offset : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~nondet10, main_#t~nondet11, main_#t~nondet12, main_#t~malloc13.base, main_#t~malloc13.offset, main_#t~malloc14.base, main_~n~0, main_~length1~0, main_#t~ret15.offset, main_~nondetString2~0.base, main_~nondetString2~0.offset, main_#t~ret15.base, main_~nondetString1~0.base, main_~nondetString1~0.offset, main_#t~malloc14.offset, main_~length2~0;
    assume 0 <= main_#t~nondet10 + 2147483648 && main_#t~nondet10 <= 2147483647;
    main_~length1~0 := main_#t~nondet10;
    havoc main_#t~nondet10;
    assume 0 <= main_#t~nondet11 + 2147483648 && main_#t~nondet11 <= 2147483647;
    main_~length2~0 := main_#t~nondet11;
    havoc main_#t~nondet11;
    assume 0 <= main_#t~nondet12 + 2147483648 && main_#t~nondet12 <= 2147483647;
    main_~n~0 := main_#t~nondet12;
    havoc main_#t~nondet12;
    assume !(main_~length1~0 < 1);
    assume !(main_~length2~0 < 1);
    assume !(main_~n~0 < 1);
    assume !(main_~length1~0 < main_~n~0) && !(main_~length1~0 < main_~length2~0 + main_~n~0);
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := main_~length1~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc13.base, main_#t~malloc13.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~nondetString1~0.base, main_~nondetString1~0.offset := main_#t~malloc13.base, main_#t~malloc13.offset;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := main_~length2~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #length == #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size];
    main_#t~malloc14.base, main_#t~malloc14.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~nondetString2~0.base, main_~nondetString2~0.offset := main_#t~malloc14.base, main_#t~malloc14.offset;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 1, main_~nondetString1~0.base, 0, main_~nondetString1~0.offset + -1 * main_~n~0 + main_~length1~0 + -1;
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
    cstrncat_#in~n, cstrncat_#in~s2.offset, cstrncat_#in~s1.base, cstrncat_#in~s1.offset, cstrncat_#in~s2.base := main_~n~0, main_~nondetString2~0.offset, main_~nondetString1~0.base, main_~nondetString1~0.offset, main_~nondetString2~0.base;
    havoc cstrncat_#res.offset, cstrncat_#res.base;
    havoc cstrncat_#t~post3.offset, cstrncat_~n, cstrncat_#t~short6, cstrncat_#t~post4.offset, cstrncat_~s~0.base, cstrncat_#t~post8.offset, cstrncat_#t~post8.base, cstrncat_~s1.base, cstrncat_~s2.base, cstrncat_#t~mem9, cstrncat_#t~mem2, cstrncat_#t~mem5, cstrncat_#t~post7, cstrncat_~s2.offset, cstrncat_#t~post3.base, cstrncat_#t~post4.base, cstrncat_~s~0.offset, cstrncat_~s1.offset;
    cstrncat_~s1.base, cstrncat_~s1.offset := cstrncat_#in~s1.base, cstrncat_#in~s1.offset;
    cstrncat_~s2.base, cstrncat_~s2.offset := cstrncat_#in~s2.base, cstrncat_#in~s2.offset;
    cstrncat_~n := cstrncat_#in~n;
    cstrncat_~s~0.base, cstrncat_~s~0.offset := cstrncat_~s1.base, cstrncat_~s1.offset;
    goto loc1;
  loc1:
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := cstrncat_~s~0.base, cstrncat_~s~0.offset, 1;
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
    cstrncat_#t~mem2 := read~int_#value;
    assume !(cstrncat_#t~mem2 == 0);
    havoc cstrncat_#t~mem2;
    cstrncat_#t~post3.offset, cstrncat_#t~post3.base := cstrncat_~s~0.offset, cstrncat_~s~0.base;
    cstrncat_~s~0.base, cstrncat_~s~0.offset := cstrncat_#t~post3.base, cstrncat_#t~post3.offset + 1;
    havoc cstrncat_#t~post3.offset, cstrncat_#t~post3.base;
    goto loc1;
  loc3:
    assert false;
}

