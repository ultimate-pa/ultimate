var #memory_$Pointer$.base : [int][int]int;

var #valid : [int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

var #memory_$Pointer$.offset : [int][int]int;

procedure ULTIMATE.start() returns ()
modifies #memory_$Pointer$.base, #valid, #NULL.offset, #length, #NULL.base, #memory_$Pointer$.offset;
{
    var main_#t~nondet1 : int;
    var read~$Pointer$_#value.base : int;
    var main_#t~mem6.offset : int;
    var write~$Pointer$_#sizeOfWrittenType : int;
    var main_#t~nondet3 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var read~$Pointer$_#value.offset : int;
    var read~$Pointer$_#sizeOfReadType : int;
    var ULTIMATE.dealloc_~addr.offset : int;
    var main_#t~malloc0.base : int;
    var main_#t~malloc2.base : int;
    var main_~list~0.base : int;
    var write~$Pointer$_#value.offset : int;
    var ULTIMATE.dealloc_~addr.base : int;
    var main_#t~mem8.offset : int;
    var main_~y~0.base : int;
    var main_#t~mem6.base : int;
    var main_#t~mem7.base : int;
    var main_#t~mem8.base : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var write~$Pointer$_old_#memory_$Pointer$.base : [int][int]int;
    var main_~list~0.offset : int;
    var #Ultimate.alloc_~size : int;
    var main_#t~malloc0.offset : int;
    var main_#t~malloc5.base : int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var read~$Pointer$_#ptr.offset : int;
    var write~$Pointer$_#ptr.base : int;
    var ULTIMATE.dealloc_old_#valid : [int]int;
    var main_#t~mem7.offset : int;
    var write~$Pointer$_#value.base : int;
    var write~$Pointer$_#ptr.offset : int;
    var main_#t~malloc2.offset : int;
    var main_#res : int;
    var write~$Pointer$_old_#memory_$Pointer$.offset : [int][int]int;
    var read~$Pointer$_#ptr.base : int;
    var main_~y~0.offset : int;
    var main_#t~malloc5.offset : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~nondet1, main_~list~0.offset, main_#t~mem6.offset, main_#t~nondet3, main_#t~malloc0.offset, main_#t~malloc5.base, main_#t~malloc0.base, main_#t~mem7.offset, main_#t~malloc2.base, main_#t~malloc2.offset, main_~list~0.base, main_#t~mem8.offset, main_~y~0.base, main_~y~0.offset, main_#t~malloc5.offset, main_#t~mem6.base, main_#t~mem7.base, main_#t~mem8.base;
    main_~list~0.offset, main_~list~0.base := 0, 0;
    main_~y~0.base, main_~y~0.offset := 0, 0;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 13;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc0.base, main_#t~malloc0.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~y~0.base, main_~y~0.offset := main_#t~malloc0.base, main_#t~malloc0.offset;
    write~$Pointer$_old_#memory_$Pointer$.base, write~$Pointer$_old_#memory_$Pointer$.offset := #memory_$Pointer$.base, #memory_$Pointer$.offset;
    write~$Pointer$_#value.base, write~$Pointer$_#ptr.offset, write~$Pointer$_#sizeOfWrittenType, write~$Pointer$_#value.offset, write~$Pointer$_#ptr.base := 0, main_~y~0.offset, 4, 0, main_~y~0.base;
    assume 1 == #valid[write~$Pointer$_#ptr.base];
    assume write~$Pointer$_#sizeOfWrittenType + write~$Pointer$_#ptr.offset <= #length[write~$Pointer$_#ptr.base] && 0 <= write~$Pointer$_#ptr.offset;
    assume 1 == #valid[write~$Pointer$_#ptr.base];
    assume write~$Pointer$_#sizeOfWrittenType + write~$Pointer$_#ptr.offset <= #length[write~$Pointer$_#ptr.base] && 0 <= write~$Pointer$_#ptr.offset;
    havoc #memory_$Pointer$.base, #memory_$Pointer$.offset;
    assume #memory_$Pointer$.offset == write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.offset]] && #memory_$Pointer$.base == write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.base]];
    write~$Pointer$_old_#memory_$Pointer$.base, write~$Pointer$_old_#memory_$Pointer$.offset := #memory_$Pointer$.base, #memory_$Pointer$.offset;
    write~$Pointer$_#value.base, write~$Pointer$_#ptr.offset, write~$Pointer$_#sizeOfWrittenType, write~$Pointer$_#value.offset, write~$Pointer$_#ptr.base := 0, main_~y~0.offset + 4, 4, 0, main_~y~0.base;
    assume 1 == #valid[write~$Pointer$_#ptr.base];
    assume write~$Pointer$_#ptr.offset + write~$Pointer$_#sizeOfWrittenType <= #length[write~$Pointer$_#ptr.base] && 0 <= write~$Pointer$_#ptr.offset;
    assume #valid[write~$Pointer$_#ptr.base] == 1;
    assume write~$Pointer$_#ptr.offset + write~$Pointer$_#sizeOfWrittenType <= #length[write~$Pointer$_#ptr.base] && 0 <= write~$Pointer$_#ptr.offset;
    havoc #memory_$Pointer$.base, #memory_$Pointer$.offset;
    assume #memory_$Pointer$.base == write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.base]] && #memory_$Pointer$.offset == write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.offset]];
    write~$Pointer$_old_#memory_$Pointer$.base, write~$Pointer$_old_#memory_$Pointer$.offset := #memory_$Pointer$.base, #memory_$Pointer$.offset;
    write~$Pointer$_#value.base, write~$Pointer$_#ptr.offset, write~$Pointer$_#sizeOfWrittenType, write~$Pointer$_#value.offset, write~$Pointer$_#ptr.base := main_~y~0.base, main_~y~0.offset + 8, 4, main_~y~0.offset + 12, main_~y~0.base;
    assume 1 == #valid[write~$Pointer$_#ptr.base];
    assume 0 <= write~$Pointer$_#ptr.offset && write~$Pointer$_#ptr.offset + write~$Pointer$_#sizeOfWrittenType <= #length[write~$Pointer$_#ptr.base];
    assume 1 == #valid[write~$Pointer$_#ptr.base];
    assume write~$Pointer$_#sizeOfWrittenType + write~$Pointer$_#ptr.offset <= #length[write~$Pointer$_#ptr.base] && 0 <= write~$Pointer$_#ptr.offset;
    havoc #memory_$Pointer$.base, #memory_$Pointer$.offset;
    assume #memory_$Pointer$.offset == write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.offset]] && write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.base]] == #memory_$Pointer$.base;
    main_~list~0.offset, main_~list~0.base := main_~y~0.offset, main_~y~0.base;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    assume 0 == main_#t~nondet1;
    havoc main_#t~nondet1;
    goto loc1;
  loc1:
    assume !(0 == main_~list~0.offset) || !(0 == main_~list~0.base);
    main_~y~0.base, main_~y~0.offset := main_~list~0.base, main_~list~0.offset;
    read~$Pointer$_#ptr.base, read~$Pointer$_#sizeOfReadType, read~$Pointer$_#ptr.offset := main_~list~0.base, 4, main_~list~0.offset;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(1 == #valid[read~$Pointer$_#ptr.base]);
    goto loc3;
  loc2_1:
    assume 1 == #valid[read~$Pointer$_#ptr.base];
    assume 0 <= read~$Pointer$_#ptr.offset && read~$Pointer$_#sizeOfReadType + read~$Pointer$_#ptr.offset <= #length[read~$Pointer$_#ptr.base];
    assume 1 == #valid[read~$Pointer$_#ptr.base];
    assume 0 <= read~$Pointer$_#ptr.offset && read~$Pointer$_#sizeOfReadType + read~$Pointer$_#ptr.offset <= #length[read~$Pointer$_#ptr.base];
    havoc read~$Pointer$_#value.base, read~$Pointer$_#value.offset;
    assume read~$Pointer$_#value.base == #memory_$Pointer$.base[read~$Pointer$_#ptr.base][read~$Pointer$_#ptr.offset] && read~$Pointer$_#value.offset == #memory_$Pointer$.offset[read~$Pointer$_#ptr.base][read~$Pointer$_#ptr.offset];
    main_#t~mem6.offset, main_#t~mem6.base := read~$Pointer$_#value.offset, read~$Pointer$_#value.base;
    main_~list~0.offset, main_~list~0.base := main_#t~mem6.offset, main_#t~mem6.base;
    havoc main_#t~mem6.offset, main_#t~mem6.base;
    read~$Pointer$_#ptr.base, read~$Pointer$_#sizeOfReadType, read~$Pointer$_#ptr.offset := main_~y~0.base, 4, main_~y~0.offset + 8;
    assume #valid[read~$Pointer$_#ptr.base] == 1;
    assume 0 <= read~$Pointer$_#ptr.offset && read~$Pointer$_#ptr.offset + read~$Pointer$_#sizeOfReadType <= #length[read~$Pointer$_#ptr.base];
    assume #valid[read~$Pointer$_#ptr.base] == 1;
    assume read~$Pointer$_#ptr.offset + read~$Pointer$_#sizeOfReadType <= #length[read~$Pointer$_#ptr.base] && 0 <= read~$Pointer$_#ptr.offset;
    havoc read~$Pointer$_#value.base, read~$Pointer$_#value.offset;
    assume read~$Pointer$_#value.base == #memory_$Pointer$.base[read~$Pointer$_#ptr.base][read~$Pointer$_#ptr.offset] && read~$Pointer$_#value.offset == #memory_$Pointer$.offset[read~$Pointer$_#ptr.base][read~$Pointer$_#ptr.offset];
    main_#t~mem7.offset, main_#t~mem7.base := read~$Pointer$_#value.offset, read~$Pointer$_#value.base;
    assume main_~y~0.base == main_#t~mem7.base && main_~y~0.offset + 12 == main_#t~mem7.offset;
    havoc main_#t~mem7.offset, main_#t~mem7.base;
    assume 0 == main_~y~0.offset;
    assume 0 == main_~y~0.base || #valid[main_~y~0.base] == 1;
    ULTIMATE.dealloc_old_#valid := #valid;
    ULTIMATE.dealloc_~addr.base, ULTIMATE.dealloc_~addr.offset := main_~y~0.base, main_~y~0.offset;
    havoc #valid;
    assume #valid == ULTIMATE.dealloc_old_#valid[ULTIMATE.dealloc_~addr.base := 0];
    goto loc1;
  loc3:
    assert false;
}

