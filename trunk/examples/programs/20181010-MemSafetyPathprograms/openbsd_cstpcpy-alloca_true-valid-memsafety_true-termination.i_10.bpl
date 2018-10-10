var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var cstpcpy_#t~mem4 : int;
    var read~int_#value : int;
    var main_~nondetArea~0.offset : int;
    var cstpcpy_#res.base : int;
    var main_#t~nondet5 : int;
    var cstpcpy_#in~to.offset : int;
    var main_~nondetString~0.offset : int;
    var main_~nondetArea~0.base : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~ret9.offset : int;
    var main_#t~nondet6 : int;
    var write~int_#ptr.offset : int;
    var main_#t~malloc7.offset : int;
    var write~int_#ptr.base : int;
    var cstpcpy_#t~pre2.base : int;
    var cstpcpy_#t~pre3.base : int;
    var cstpcpy_#t~pre3.offset : int;
    var main_~length2~0 : int;
    var #Ultimate.alloc_#res.base : int;
    var cstpcpy_~to.base : int;
    var main_#t~malloc8.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var main_#t~malloc7.base : int;
    var cstpcpy_#in~from.offset : int;
    var #Ultimate.alloc_~size : int;
    var main_~length1~0 : int;
    var write~int_old_#memory_int : [int][int]int;
    var cstpcpy_#res.offset : int;
    var read~int_#sizeOfReadType : int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var cstpcpy_~from.offset : int;
    var write~int_#sizeOfWrittenType : int;
    var read~int_#ptr.base : int;
    var cstpcpy_#t~pre2.offset : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_~nondetString~0.base : int;
    var main_#t~malloc8.offset : int;
    var cstpcpy_#in~from.base : int;
    var write~int_#value : int;
    var main_#t~ret9.base : int;
    var cstpcpy_~from.base : int;
    var cstpcpy_#in~to.base : int;
    var cstpcpy_~to.offset : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~malloc8.base, main_#t~malloc7.base, main_~nondetArea~0.offset, main_#t~nondet5, main_~nondetString~0.offset, main_~nondetArea~0.base, main_#t~ret9.offset, main_~length1~0, main_#t~nondet6, main_#t~malloc7.offset, main_~nondetString~0.base, main_#t~malloc8.offset, main_#t~ret9.base, main_~length2~0;
    assume main_#t~nondet5 <= 2147483647 && 0 <= main_#t~nondet5 + 2147483648;
    main_~length1~0 := main_#t~nondet5;
    havoc main_#t~nondet5;
    assume main_#t~nondet6 <= 2147483647 && 0 <= main_#t~nondet6 + 2147483648;
    main_~length2~0 := main_#t~nondet6;
    havoc main_#t~nondet6;
    assume !(main_~length1~0 < 1);
    assume !(main_~length2~0 < 1);
    assume !(main_~length1~0 < main_~length2~0);
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := main_~length1~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc7.base, main_#t~malloc7.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~nondetArea~0.offset, main_~nondetArea~0.base := main_#t~malloc7.offset, main_#t~malloc7.base;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := main_~length2~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #length == #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size];
    main_#t~malloc8.base, main_#t~malloc8.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~nondetString~0.base, main_~nondetString~0.offset := main_#t~malloc8.base, main_#t~malloc8.offset;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 1, main_~nondetString~0.base, 0, main_~length2~0 + main_~nondetString~0.offset + -1;
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    assume 1 == #valid[write~int_#ptr.base];
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    havoc #memory_int;
    assume #memory_int == write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]];
    cstpcpy_#in~from.offset, cstpcpy_#in~to.offset, cstpcpy_#in~from.base, cstpcpy_#in~to.base := main_~nondetString~0.offset, main_~nondetArea~0.offset, main_~nondetString~0.base, main_~nondetArea~0.base;
    havoc cstpcpy_#res.base, cstpcpy_#res.offset;
    havoc cstpcpy_#t~mem4, cstpcpy_#t~pre2.offset, cstpcpy_#t~pre2.base, cstpcpy_#t~pre3.base, cstpcpy_~from.base, cstpcpy_#t~pre3.offset, cstpcpy_~from.offset, cstpcpy_~to.base, cstpcpy_~to.offset;
    cstpcpy_~to.base, cstpcpy_~to.offset := cstpcpy_#in~to.base, cstpcpy_#in~to.offset;
    cstpcpy_~from.base, cstpcpy_~from.offset := cstpcpy_#in~from.base, cstpcpy_#in~from.offset;
    goto loc1;
  loc1:
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := cstpcpy_~from.base, cstpcpy_~from.offset, 1;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume read~int_#value == #memory_int[read~int_#ptr.base][read~int_#ptr.offset];
    cstpcpy_#t~mem4 := read~int_#value;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 1, cstpcpy_~to.base, cstpcpy_#t~mem4, cstpcpy_~to.offset;
    assume 1 == #valid[write~int_#ptr.base];
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(0 <= write~int_#ptr.offset) || !(write~int_#ptr.offset + write~int_#sizeOfWrittenType <= #length[write~int_#ptr.base]);
    goto loc3;
  loc2_1:
    assume write~int_#ptr.offset + write~int_#sizeOfWrittenType <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    assume 1 == #valid[write~int_#ptr.base];
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    havoc #memory_int;
    assume write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]] == #memory_int;
    assume !(cstpcpy_#t~mem4 == 0);
    havoc cstpcpy_#t~mem4;
    cstpcpy_#t~pre2.offset, cstpcpy_#t~pre2.base := cstpcpy_~from.offset + 1, cstpcpy_~from.base;
    cstpcpy_~from.base, cstpcpy_~from.offset := cstpcpy_~from.base, cstpcpy_~from.offset + 1;
    havoc cstpcpy_#t~pre2.offset, cstpcpy_#t~pre2.base;
    cstpcpy_#t~pre3.base, cstpcpy_#t~pre3.offset := cstpcpy_~to.base, cstpcpy_~to.offset + 1;
    cstpcpy_~to.offset, cstpcpy_~to.base := cstpcpy_~to.offset + 1, cstpcpy_~to.base;
    havoc cstpcpy_#t~pre3.base, cstpcpy_#t~pre3.offset;
    goto loc1;
  loc3:
    assert false;
}

