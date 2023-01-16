var #memory_$Pointer$.base : [int][int]int;

var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

var #memory_$Pointer$.offset : [int][int]int;

procedure ULTIMATE.start() returns ()
modifies #memory_$Pointer$.base, #valid, #memory_int, #NULL.offset, #length, #NULL.base, #memory_$Pointer$.offset;
{
    var read~int_#value : int;
    var main_#t~nondet4 : int;
    var write~$Pointer$_#sizeOfWrittenType : int;
    var read~$Pointer$_#value.offset : int;
    var main_#t~nondet6 : int;
    var main_~head~0.base : int;
    var write~int_#ptr.base : int;
    var write~$Pointer$_old_#memory_int : [int][int]int;
    var main_#t~mem8.offset : int;
    var main_~y~0.base : int;
    var main_#t~mem13.base : int;
    var main_#t~mem15.base : int;
    var main_#t~mem16.base : int;
    var main_#t~mem12.base : int;
    var main_#t~mem14 : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var write~int_old_#memory_$Pointer$.offset : [int][int]int;
    var main_#t~malloc5.base : int;
    var write~int_old_#memory_int : [int][int]int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var read~$Pointer$_#ptr.offset : int;
    var write~$Pointer$_#ptr.base : int;
    var main_#t~mem7.offset : int;
    var write~$Pointer$_#ptr.offset : int;
    var write~int_#sizeOfWrittenType : int;
    var main_~head~0.offset : int;
    var read~int_#ptr.base : int;
    var main_#t~malloc2.offset : int;
    var write~int_#value : int;
    var main_~y~0.offset : int;
    var main_#t~nondet1 : int;
    var read~$Pointer$_#value.base : int;
    var main_~x~0.offset : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_~x~0.base : int;
    var read~$Pointer$_#sizeOfReadType : int;
    var main_#t~mem9.offset : int;
    var write~int_#ptr.offset : int;
    var main_#t~malloc0.base : int;
    var main_#t~malloc2.base : int;
    var main_#t~mem13.offset : int;
    var main_#t~mem15.offset : int;
    var write~$Pointer$_#value.offset : int;
    var main_#t~mem3.offset : int;
    var main_#t~mem3.base : int;
    var main_#t~mem9.base : int;
    var main_#t~mem7.base : int;
    var main_#t~mem8.base : int;
    var main_#t~malloc10.offset : int;
    var main_#t~mem11 : int;
    var write~$Pointer$_old_#memory_$Pointer$.base : [int][int]int;
    var #Ultimate.alloc_~size : int;
    var write~int_old_#memory_$Pointer$.base : [int][int]int;
    var main_#t~malloc0.offset : int;
    var main_#t~mem12.offset : int;
    var read~int_#sizeOfReadType : int;
    var main_#t~mem16.offset : int;
    var write~$Pointer$_#value.base : int;
    var main_#t~malloc10.base : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var write~$Pointer$_old_#memory_$Pointer$.offset : [int][int]int;
    var read~$Pointer$_#ptr.base : int;
    var main_#t~malloc5.offset : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~nondet1, main_#t~nondet4, main_~x~0.offset, main_#t~nondet6, main_~x~0.base, main_#t~mem9.offset, main_#t~malloc0.base, main_~head~0.base, main_#t~malloc2.base, main_#t~mem13.offset, main_#t~mem15.offset, main_#t~mem8.offset, main_~y~0.base, main_#t~mem13.base, main_#t~mem15.base, main_#t~mem3.offset, main_#t~mem3.base, main_#t~mem16.base, main_#t~mem12.base, main_#t~mem14, main_#t~mem9.base, main_#t~mem7.base, main_#t~mem8.base, main_#t~malloc10.offset, main_#t~mem11, main_#t~malloc0.offset, main_#t~malloc5.base, main_#t~mem12.offset, main_#t~mem16.offset, main_#t~mem7.offset, main_~head~0.offset, main_#t~malloc10.base, main_#t~malloc2.offset, main_~y~0.offset, main_#t~malloc5.offset;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 8;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc0.base, main_#t~malloc0.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~head~0.base, main_~head~0.offset := main_#t~malloc0.base, main_#t~malloc0.offset;
    write~$Pointer$_old_#memory_$Pointer$.base, write~$Pointer$_old_#memory_$Pointer$.offset, write~$Pointer$_old_#memory_int := #memory_$Pointer$.base, #memory_$Pointer$.offset, #memory_int;
    write~$Pointer$_#value.base, write~$Pointer$_#ptr.offset, write~$Pointer$_#sizeOfWrittenType, write~$Pointer$_#value.offset, write~$Pointer$_#ptr.base := 0, main_~head~0.offset, 4, 0, main_~head~0.base;
    assume 1 == #valid[write~$Pointer$_#ptr.base];
    assume write~$Pointer$_#sizeOfWrittenType + write~$Pointer$_#ptr.offset <= #length[write~$Pointer$_#ptr.base] && 0 <= write~$Pointer$_#ptr.offset;
    assume 1 == #valid[write~$Pointer$_#ptr.base];
    assume write~$Pointer$_#sizeOfWrittenType + write~$Pointer$_#ptr.offset <= #length[write~$Pointer$_#ptr.base] && 0 <= write~$Pointer$_#ptr.offset;
    havoc #memory_$Pointer$.base, #memory_$Pointer$.offset;
    assume (#memory_$Pointer$.offset == write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.offset]] && #memory_$Pointer$.base == write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.base]]) && #memory_int == write~$Pointer$_old_#memory_int[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_int[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := #memory_int[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset]]];
    write~int_old_#memory_$Pointer$.offset, write~int_old_#memory_$Pointer$.base, write~int_old_#memory_int := #memory_$Pointer$.offset, #memory_$Pointer$.base, #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, main_~head~0.base, 0, main_~head~0.offset + 4;
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    assume 1 == #valid[write~int_#ptr.base];
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    havoc #memory_int;
    assume (#memory_$Pointer$.offset == write~int_old_#memory_$Pointer$.offset[write~int_#ptr.base := write~int_old_#memory_$Pointer$.offset[write~int_#ptr.base][write~int_#ptr.offset := #memory_$Pointer$.offset[write~int_#ptr.base][write~int_#ptr.offset]]] && #memory_int == write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]]) && write~int_old_#memory_$Pointer$.base[write~int_#ptr.base := write~int_old_#memory_$Pointer$.base[write~int_#ptr.base][write~int_#ptr.offset := #memory_$Pointer$.base[write~int_#ptr.base][write~int_#ptr.offset]]] == #memory_$Pointer$.base;
    main_~x~0.offset, main_~x~0.base := main_~head~0.offset, main_~head~0.base;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    assume 0 == main_#t~nondet1;
    havoc main_#t~nondet1;
    assume main_#t~nondet4 <= 2147483647 && 0 <= main_#t~nondet4 + 2147483648;
    assume !(0 == main_#t~nondet4);
    havoc main_#t~nondet4;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 8;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #length == #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size];
    main_#t~malloc5.base, main_#t~malloc5.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~x~0.offset, main_~x~0.base := main_#t~malloc5.offset, main_#t~malloc5.base;
    write~int_old_#memory_$Pointer$.offset, write~int_old_#memory_$Pointer$.base, write~int_old_#memory_int := #memory_$Pointer$.offset, #memory_$Pointer$.base, #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, main_~x~0.base, 1, main_~x~0.offset + 4;
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    havoc #memory_int;
    assume (write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]] == #memory_int && #memory_$Pointer$.base == write~int_old_#memory_$Pointer$.base[write~int_#ptr.base := write~int_old_#memory_$Pointer$.base[write~int_#ptr.base][write~int_#ptr.offset := #memory_$Pointer$.base[write~int_#ptr.base][write~int_#ptr.offset]]]) && #memory_$Pointer$.offset == write~int_old_#memory_$Pointer$.offset[write~int_#ptr.base := write~int_old_#memory_$Pointer$.offset[write~int_#ptr.base][write~int_#ptr.offset := #memory_$Pointer$.offset[write~int_#ptr.base][write~int_#ptr.offset]]];
    write~$Pointer$_old_#memory_$Pointer$.base, write~$Pointer$_old_#memory_$Pointer$.offset, write~$Pointer$_old_#memory_int := #memory_$Pointer$.base, #memory_$Pointer$.offset, #memory_int;
    write~$Pointer$_#value.base, write~$Pointer$_#ptr.offset, write~$Pointer$_#sizeOfWrittenType, write~$Pointer$_#value.offset, write~$Pointer$_#ptr.base := main_~head~0.base, main_~x~0.offset, 4, main_~head~0.offset, main_~x~0.base;
    assume 1 == #valid[write~$Pointer$_#ptr.base];
    assume write~$Pointer$_#sizeOfWrittenType + write~$Pointer$_#ptr.offset <= #length[write~$Pointer$_#ptr.base] && 0 <= write~$Pointer$_#ptr.offset;
    assume 1 == #valid[write~$Pointer$_#ptr.base];
    assume write~$Pointer$_#sizeOfWrittenType + write~$Pointer$_#ptr.offset <= #length[write~$Pointer$_#ptr.base] && 0 <= write~$Pointer$_#ptr.offset;
    havoc #memory_$Pointer$.base, #memory_$Pointer$.offset;
    assume (write~$Pointer$_old_#memory_int[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_int[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := #memory_int[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset]]] == #memory_int && write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.offset]] == #memory_$Pointer$.offset) && write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.base]] == #memory_$Pointer$.base;
    main_~head~0.base, main_~head~0.offset := main_~x~0.base, main_~x~0.offset;
    main_~x~0.offset, main_~x~0.base := main_~head~0.offset, main_~head~0.base;
    goto loc1;
  loc1:
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := main_~x~0.base, main_~x~0.offset + 4, 4;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(#valid[read~int_#ptr.base] == 1);
    goto loc3;
  loc2_1:
    assume #valid[read~int_#ptr.base] == 1;
    assume 0 <= read~int_#ptr.offset && read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base];
    assume 1 == #valid[read~int_#ptr.base];
    assume 0 <= read~int_#ptr.offset && read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base];
    havoc read~int_#value;
    assume read~int_#value == #memory_int[read~int_#ptr.base][read~int_#ptr.offset];
    main_#t~mem11 := read~int_#value;
    assume !(main_#t~mem11 == 1);
    havoc main_#t~mem11;
    read~$Pointer$_#ptr.base, read~$Pointer$_#sizeOfReadType, read~$Pointer$_#ptr.offset := main_~x~0.base, 4, main_~x~0.offset;
    assume 1 == #valid[read~$Pointer$_#ptr.base];
    assume 0 <= read~$Pointer$_#ptr.offset && read~$Pointer$_#sizeOfReadType + read~$Pointer$_#ptr.offset <= #length[read~$Pointer$_#ptr.base];
    assume #valid[read~$Pointer$_#ptr.base] == 1;
    assume 0 <= read~$Pointer$_#ptr.offset && read~$Pointer$_#ptr.offset + read~$Pointer$_#sizeOfReadType <= #length[read~$Pointer$_#ptr.base];
    havoc read~$Pointer$_#value.base, read~$Pointer$_#value.offset;
    assume read~$Pointer$_#value.base == #memory_$Pointer$.base[read~$Pointer$_#ptr.base][read~$Pointer$_#ptr.offset] && #memory_$Pointer$.offset[read~$Pointer$_#ptr.base][read~$Pointer$_#ptr.offset] == read~$Pointer$_#value.offset;
    main_#t~mem12.offset, main_#t~mem12.base := read~$Pointer$_#value.offset, read~$Pointer$_#value.base;
    main_~x~0.offset, main_~x~0.base := main_#t~mem12.offset, main_#t~mem12.base;
    havoc main_#t~mem12.offset, main_#t~mem12.base;
    goto loc1;
  loc3:
    assert false;
}

