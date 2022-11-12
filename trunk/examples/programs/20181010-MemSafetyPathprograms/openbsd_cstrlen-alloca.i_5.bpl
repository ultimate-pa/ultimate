var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var cstrlen_#in~str.base : int;
    var read~int_#value : int;
    var main_#t~nondet4 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var cstrlen_#in~str.offset : int;
    var write~int_#ptr.offset : int;
    var write~int_#ptr.base : int;
    var main_~nondetString1~0.base : int;
    var cstrlen_~str.base : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var #Ultimate.alloc_~size : int;
    var cstrlen_#t~pre2.base : int;
    var main_~length1~0 : int;
    var main_#t~malloc5.base : int;
    var write~int_old_#memory_int : [int][int]int;
    var read~int_#sizeOfReadType : int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var cstrlen_~str.offset : int;
    var write~int_#sizeOfWrittenType : int;
    var cstrlen_~s~0.base : int;
    var read~int_#ptr.base : int;
    var cstrlen_#res : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_~nondetString1~0.offset : int;
    var write~int_#value : int;
    var cstrlen_~s~0.offset : int;
    var cstrlen_#t~mem3 : int;
    var main_#t~ret6 : int;
    var cstrlen_#t~pre2.offset : int;
    var main_#t~malloc5.offset : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~nondet4, main_~nondetString1~0.base, main_~length1~0, main_~nondetString1~0.offset, main_#t~malloc5.base, main_#t~ret6, main_#t~malloc5.offset;
    assume main_#t~nondet4 <= 2147483647 && 0 <= main_#t~nondet4 + 2147483648;
    main_~length1~0 := main_#t~nondet4;
    havoc main_#t~nondet4;
    assume !(main_~length1~0 < 1);
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := main_~length1~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc5.base, main_#t~malloc5.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~nondetString1~0.base, main_~nondetString1~0.offset := main_#t~malloc5.base, main_#t~malloc5.offset;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 1, main_~nondetString1~0.base, 0, main_~nondetString1~0.offset + main_~length1~0 + -1;
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    havoc #memory_int;
    assume #memory_int == write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]];
    cstrlen_#in~str.base, cstrlen_#in~str.offset := main_~nondetString1~0.base, main_~nondetString1~0.offset;
    havoc cstrlen_#res;
    havoc cstrlen_~s~0.base, cstrlen_#t~pre2.base, cstrlen_~s~0.offset, cstrlen_#t~mem3, cstrlen_#t~pre2.offset, cstrlen_~str.base, cstrlen_~str.offset;
    cstrlen_~str.base, cstrlen_~str.offset := cstrlen_#in~str.base, cstrlen_#in~str.offset;
    havoc cstrlen_~s~0.base, cstrlen_~s~0.offset;
    cstrlen_~s~0.base, cstrlen_~s~0.offset := cstrlen_~str.base, cstrlen_~str.offset;
    goto loc1;
  loc1:
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := cstrlen_~s~0.base, cstrlen_~s~0.offset, 1;
    assume 1 == #valid[read~int_#ptr.base];
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base]) || !(0 <= read~int_#ptr.offset);
    goto loc3;
  loc2_1:
    assume 0 <= read~int_#ptr.offset && read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base];
    assume #valid[read~int_#ptr.base] == 1;
    assume 0 <= read~int_#ptr.offset && read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base];
    havoc read~int_#value;
    assume read~int_#value == #memory_int[read~int_#ptr.base][read~int_#ptr.offset];
    cstrlen_#t~mem3 := read~int_#value;
    assume !(0 == cstrlen_#t~mem3);
    havoc cstrlen_#t~mem3;
    cstrlen_#t~pre2.base, cstrlen_#t~pre2.offset := cstrlen_~s~0.base, cstrlen_~s~0.offset + 1;
    cstrlen_~s~0.base, cstrlen_~s~0.offset := cstrlen_~s~0.base, cstrlen_~s~0.offset + 1;
    havoc cstrlen_#t~pre2.base, cstrlen_#t~pre2.offset;
    goto loc1;
  loc3:
    assert false;
}

