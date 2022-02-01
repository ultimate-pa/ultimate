var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var read~int_#value : int;
    var lis_#in~a.offset : int;
    var main_#t~malloc17.base : int;
    var main_#t~malloc17.offset : int;
    var lis_#res : int;
    var lis_~max~0 : int;
    var lis_#t~post6 : int;
    var lis_~best~0.offset : int;
    var write~int_#ptr.base : int;
    var lis_~prev~0.base : int;
    var main_~numbers~0.base : int;
    var ULTIMATE.dealloc_~addr.base : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var lis_#t~post13 : int;
    var lis_~j~0 : int;
    var lis_#t~mem8 : int;
    var lis_~a.offset : int;
    var write~int_old_#memory_int : [int][int]int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var ULTIMATE.dealloc_old_#valid : [int]int;
    var lis_#t~malloc3.base : int;
    var write~int_#sizeOfWrittenType : int;
    var lis_~i~0 : int;
    var lis_#t~mem15 : int;
    var read~int_#ptr.base : int;
    var write~int_#value : int;
    var lis_~best~0.base : int;
    var lis_#t~malloc2.offset : int;
    var lis_#t~post5 : int;
    var lis_~a.base : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var lis_#in~N : int;
    var write~int_#ptr.offset : int;
    var lis_#t~mem10 : int;
    var ULTIMATE.dealloc_~addr.offset : int;
    var lis_~N : int;
    var lis_~prev~0.offset : int;
    var lis_#t~mem7 : int;
    var lis_#t~mem9 : int;
    var lis_#t~short11 : bool;
    var #Ultimate.alloc_~size : int;
    var read~int_#sizeOfReadType : int;
    var main_#t~ret18 : int;
    var lis_#t~mem12 : int;
    var lis_#t~mem14 : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_~array_size~0 : int;
    var main_~numbers~0.offset : int;
    var main_#t~nondet16 : int;
    var lis_#t~post4 : int;
    var lis_#t~malloc2.base : int;
    var lis_#in~a.base : int;
    var lis_#t~malloc3.offset : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~malloc17.base, main_#t~malloc17.offset, main_~array_size~0, main_~numbers~0.base, main_~numbers~0.offset, main_#t~nondet16, main_#t~ret18;
    assume 0 <= main_#t~nondet16 + 2147483648 && main_#t~nondet16 <= 2147483647;
    main_~array_size~0 := main_#t~nondet16;
    havoc main_#t~nondet16;
    assume !(main_~array_size~0 < 1) && !(536870911 <= main_~array_size~0);
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4 * main_~array_size~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc17.base, main_#t~malloc17.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~numbers~0.base, main_~numbers~0.offset := main_#t~malloc17.base, main_#t~malloc17.offset;
    lis_#in~a.offset, lis_#in~N, lis_#in~a.base := main_~numbers~0.offset, main_~array_size~0, main_~numbers~0.base;
    havoc lis_#res;
    havoc lis_~best~0.base, lis_#t~malloc2.offset, lis_#t~post5, lis_~max~0, lis_#t~post6, lis_~a.base, lis_~best~0.offset, lis_#t~mem10, lis_~N, lis_~prev~0.base, lis_~prev~0.offset, lis_#t~mem7, lis_#t~mem9, lis_#t~short11, lis_#t~post13, lis_~j~0, lis_#t~mem8, lis_~a.offset, lis_#t~mem12, lis_#t~malloc3.base, lis_#t~mem14, lis_~i~0, lis_#t~mem15, lis_#t~post4, lis_#t~malloc2.base, lis_#t~malloc3.offset;
    lis_~a.base, lis_~a.offset := lis_#in~a.base, lis_#in~a.offset;
    lis_~N := lis_#in~N;
    havoc lis_~best~0.base, lis_~best~0.offset;
    havoc lis_~prev~0.base, lis_~prev~0.offset;
    havoc lis_~i~0;
    havoc lis_~j~0;
    lis_~max~0 := 0;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4 * lis_~N;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #length == #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size];
    lis_#t~malloc2.offset, lis_#t~malloc2.base := #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    lis_~best~0.base, lis_~best~0.offset := lis_#t~malloc2.base, lis_#t~malloc2.offset;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4 * lis_~N;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    lis_#t~malloc3.base, lis_#t~malloc3.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    lis_~prev~0.base, lis_~prev~0.offset := lis_#t~malloc3.base, lis_#t~malloc3.offset;
    lis_~i~0 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(lis_~i~0 < lis_~N);
    lis_~i~0 := 1;
    assume !(lis_~i~0 < lis_~N);
    lis_~i~0 := 0;
    goto loc3;
  loc2_1:
    assume lis_~i~0 < lis_~N;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, lis_~best~0.base, 1, 4 * lis_~i~0 + lis_~best~0.offset;
    assume 1 == #valid[write~int_#ptr.base];
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    assume 1 == #valid[write~int_#ptr.base];
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    havoc #memory_int;
    assume #memory_int == write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]];
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, lis_~prev~0.base, lis_~i~0, 4 * lis_~i~0 + lis_~prev~0.offset;
    assume 1 == #valid[write~int_#ptr.base];
    assume write~int_#ptr.offset + write~int_#sizeOfWrittenType <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    assume 1 == #valid[write~int_#ptr.base];
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    havoc #memory_int;
    assume write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]] == #memory_int;
    lis_#t~post4 := lis_~i~0;
    lis_~i~0 := lis_#t~post4 + 1;
    havoc lis_#t~post4;
    goto loc1;
  loc3:
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume !(lis_~i~0 < lis_~N);
    lis_#res := lis_~max~0;
    ULTIMATE.dealloc_old_#valid := #valid;
    ULTIMATE.dealloc_~addr.base, ULTIMATE.dealloc_~addr.offset := lis_#t~malloc2.base, lis_#t~malloc2.offset;
    havoc #valid;
    assume #valid == ULTIMATE.dealloc_old_#valid[ULTIMATE.dealloc_~addr.base := 0];
    havoc lis_#t~malloc2.offset, lis_#t~malloc2.base;
    ULTIMATE.dealloc_old_#valid := #valid;
    ULTIMATE.dealloc_~addr.base, ULTIMATE.dealloc_~addr.offset := lis_#t~malloc3.base, lis_#t~malloc3.offset;
    havoc #valid;
    assume #valid == ULTIMATE.dealloc_old_#valid[ULTIMATE.dealloc_~addr.base := 0];
    havoc lis_#t~malloc3.base, lis_#t~malloc3.offset;
    main_#t~ret18 := lis_#res;
    assume main_#t~ret18 <= 2147483647 && 0 <= main_#t~ret18 + 2147483648;
    main_#res := main_#t~ret18;
    havoc main_#t~ret18;
    ULTIMATE.dealloc_old_#valid := #valid;
    ULTIMATE.dealloc_~addr.base, ULTIMATE.dealloc_~addr.offset := main_#t~malloc17.base, main_#t~malloc17.offset;
    havoc #valid;
    assume ULTIMATE.dealloc_old_#valid[ULTIMATE.dealloc_~addr.base := 0] == #valid;
    havoc main_#t~malloc17.base, main_#t~malloc17.offset;
    assume !(main_old_#valid == #valid);
    goto loc5;
  loc4_1:
    assume lis_~i~0 < lis_~N;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := lis_~best~0.base, 4 * lis_~i~0 + lis_~best~0.offset, 4;
    assume 1 == #valid[read~int_#ptr.base];
    assume 0 <= read~int_#ptr.offset && read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base];
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    lis_#t~mem14 := read~int_#value;
    assume !(lis_~max~0 < lis_#t~mem14);
    havoc lis_#t~mem14;
    lis_#t~post13 := lis_~i~0;
    lis_~i~0 := lis_#t~post13 + 1;
    havoc lis_#t~post13;
    goto loc3;
  loc5:
    assert false;
}

