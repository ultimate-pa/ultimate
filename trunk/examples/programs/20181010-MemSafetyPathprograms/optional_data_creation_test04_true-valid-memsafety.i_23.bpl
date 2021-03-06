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
    var write~$Pointer$_#sizeOfWrittenType : int;
    var create_data_#t~mem7.base : int;
    var main_#t~mem17.offset : int;
    var read~$Pointer$_#value.offset : int;
    var main_~#list~0.offset : int;
    var main_#t~mem17.base : int;
    var main_#t~mem18.base : int;
    var main_#t~mem19.base : int;
    var append_~node~0.base : int;
    var write~$Pointer$_old_#memory_int : [int][int]int;
    var create_data_#t~nondet8 : int;
    var create_data_~data~0.base : int;
    var main_~next~0.base : int;
    var main_#t~mem16.base : int;
    var create_data_#t~nondet2 : int;
    var main_~dataNotFinished~0 : int;
    var append_#t~mem13.base : int;
    var create_data_#t~nondet4 : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var main_#t~mem21.offset : int;
    var main_#t~mem21.base : int;
    var main_~next~0.offset : int;
    var main_old_#valid : [int]int;
    var create_data_#t~mem7.offset : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var read~$Pointer$_#ptr.offset : int;
    var create_data_#t~malloc3.base : int;
    var create_data_#t~malloc5.base : int;
    var write~$Pointer$_#ptr.base : int;
    var write~$Pointer$_#ptr.offset : int;
    var append_#t~mem13.offset : int;
    var append_#t~malloc12.base : int;
    var main_#t~mem19.offset : int;
    var create_data_#t~malloc5.offset : int;
    var main_#t~nondet15 : int;
    var main_#t~mem20.offset : int;
    var read~$Pointer$_#value.base : int;
    var append_~pointerToList.offset : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var read~$Pointer$_#sizeOfReadType : int;
    var append_#in~pointerToList.base : int;
    var append_~pointerToList.base : int;
    var write~$Pointer$_#value.offset : int;
    var create_data_#res.base : int;
    var create_data_#res.offset : int;
    var create_data_#t~nondet9 : int;
    var append_~node~0.offset : int;
    var main_#t~mem18.offset : int;
    var write~$Pointer$_old_#memory_$Pointer$.base : [int][int]int;
    var #Ultimate.alloc_~size : int;
    var main_#t~mem20.base : int;
    var create_data_~counter~0 : int;
    var main_#t~mem16.offset : int;
    var append_#t~malloc12.offset : int;
    var append_#t~ret14.base : int;
    var append_#in~pointerToList.offset : int;
    var write~$Pointer$_#value.base : int;
    var main_#res : int;
    var write~$Pointer$_old_#memory_$Pointer$.offset : [int][int]int;
    var create_data_#t~malloc3.offset : int;
    var create_data_~data~0.offset : int;
    var read~$Pointer$_#ptr.base : int;
    var append_#t~ret14.offset : int;
    var main_~#list~0.base : int;
    var create_data_#t~post6 : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~mem21.offset, main_#t~mem17.offset, main_#t~mem20.base, main_#t~mem21.base, main_~next~0.offset, main_~#list~0.offset, main_#t~mem16.offset, main_#t~mem17.base, main_#t~mem18.base, main_#t~mem19.base, main_#t~mem19.offset, main_#t~nondet15, main_#t~mem20.offset, main_~next~0.base, main_#t~mem16.base, main_~#list~0.base, main_~dataNotFinished~0, main_#t~mem18.offset;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_~#list~0.offset, main_~#list~0.base := #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    write~$Pointer$_old_#memory_$Pointer$.base, write~$Pointer$_old_#memory_$Pointer$.offset, write~$Pointer$_old_#memory_int := #memory_$Pointer$.base, #memory_$Pointer$.offset, #memory_int;
    write~$Pointer$_#value.base, write~$Pointer$_#ptr.offset, write~$Pointer$_#sizeOfWrittenType, write~$Pointer$_#value.offset, write~$Pointer$_#ptr.base := 0, main_~#list~0.offset, 4, 0, main_~#list~0.base;
    assume 1 == #valid[write~$Pointer$_#ptr.base];
    assume write~$Pointer$_#sizeOfWrittenType + write~$Pointer$_#ptr.offset <= #length[write~$Pointer$_#ptr.base] && 0 <= write~$Pointer$_#ptr.offset;
    assume 1 == #valid[write~$Pointer$_#ptr.base];
    assume write~$Pointer$_#sizeOfWrittenType + write~$Pointer$_#ptr.offset <= #length[write~$Pointer$_#ptr.base] && 0 <= write~$Pointer$_#ptr.offset;
    havoc #memory_$Pointer$.base, #memory_$Pointer$.offset;
    assume (#memory_$Pointer$.offset == write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.offset]] && #memory_$Pointer$.base == write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.base]]) && #memory_int == write~$Pointer$_old_#memory_int[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_int[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := #memory_int[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset]]];
    main_~dataNotFinished~0 := 0;
    goto loc1;
  loc1:
    append_#in~pointerToList.offset, append_#in~pointerToList.base := main_~#list~0.offset, main_~#list~0.base;
    havoc append_#t~mem13.offset, append_#t~malloc12.base, append_~pointerToList.base, append_~pointerToList.offset, append_~node~0.base, append_#t~ret14.offset, append_#t~malloc12.offset, append_~node~0.offset, append_#t~mem13.base, append_#t~ret14.base;
    append_~pointerToList.base, append_~pointerToList.offset := append_#in~pointerToList.base, append_#in~pointerToList.offset;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 8;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #length == #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size];
    append_#t~malloc12.base, append_#t~malloc12.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    append_~node~0.base, append_~node~0.offset := append_#t~malloc12.base, append_#t~malloc12.offset;
    read~$Pointer$_#ptr.base, read~$Pointer$_#sizeOfReadType, read~$Pointer$_#ptr.offset := append_~pointerToList.base, 4, append_~pointerToList.offset;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(#valid[read~$Pointer$_#ptr.base] == 1);
    goto loc3;
  loc2_1:
    assume #valid[read~$Pointer$_#ptr.base] == 1;
    assume 0 <= read~$Pointer$_#ptr.offset && read~$Pointer$_#sizeOfReadType + read~$Pointer$_#ptr.offset <= #length[read~$Pointer$_#ptr.base];
    assume #valid[read~$Pointer$_#ptr.base] == 1;
    assume read~$Pointer$_#sizeOfReadType + read~$Pointer$_#ptr.offset <= #length[read~$Pointer$_#ptr.base] && 0 <= read~$Pointer$_#ptr.offset;
    havoc read~$Pointer$_#value.base, read~$Pointer$_#value.offset;
    assume read~$Pointer$_#value.offset == #memory_$Pointer$.offset[read~$Pointer$_#ptr.base][read~$Pointer$_#ptr.offset] && #memory_$Pointer$.base[read~$Pointer$_#ptr.base][read~$Pointer$_#ptr.offset] == read~$Pointer$_#value.base;
    append_#t~mem13.offset, append_#t~mem13.base := read~$Pointer$_#value.offset, read~$Pointer$_#value.base;
    write~$Pointer$_old_#memory_$Pointer$.base, write~$Pointer$_old_#memory_$Pointer$.offset, write~$Pointer$_old_#memory_int := #memory_$Pointer$.base, #memory_$Pointer$.offset, #memory_int;
    write~$Pointer$_#value.base, write~$Pointer$_#ptr.offset, write~$Pointer$_#sizeOfWrittenType, write~$Pointer$_#value.offset, write~$Pointer$_#ptr.base := append_#t~mem13.base, append_~node~0.offset + 4, 4, append_#t~mem13.offset, append_~node~0.base;
    assume #valid[write~$Pointer$_#ptr.base] == 1;
    assume write~$Pointer$_#ptr.offset + write~$Pointer$_#sizeOfWrittenType <= #length[write~$Pointer$_#ptr.base] && 0 <= write~$Pointer$_#ptr.offset;
    assume 1 == #valid[write~$Pointer$_#ptr.base];
    assume 0 <= write~$Pointer$_#ptr.offset && write~$Pointer$_#ptr.offset + write~$Pointer$_#sizeOfWrittenType <= #length[write~$Pointer$_#ptr.base];
    havoc #memory_$Pointer$.base, #memory_$Pointer$.offset;
    assume (#memory_$Pointer$.offset == write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.offset]] && #memory_$Pointer$.base == write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.base]]) && write~$Pointer$_old_#memory_int[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_int[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := #memory_int[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset]]] == #memory_int;
    havoc append_#t~mem13.offset, append_#t~mem13.base;
    havoc create_data_#res.base, create_data_#res.offset;
    havoc create_data_#t~mem7.base, create_data_~counter~0, create_data_#t~mem7.offset, create_data_#t~malloc3.base, create_data_#t~malloc5.base, create_data_#t~malloc3.offset, create_data_#t~malloc5.offset, create_data_~data~0.offset, create_data_#t~nondet8, create_data_~data~0.base, create_data_#t~nondet9, create_data_#t~nondet2, create_data_#t~nondet4, create_data_#t~post6;
    assume 0 <= create_data_#t~nondet2 + 2147483648 && create_data_#t~nondet2 <= 2147483647;
    assume !(0 == create_data_#t~nondet2);
    havoc create_data_#t~nondet2;
    create_data_#res.base, create_data_#res.offset := 0, 0;
    append_#t~ret14.offset, append_#t~ret14.base := create_data_#res.offset, create_data_#res.base;
    write~$Pointer$_old_#memory_$Pointer$.base, write~$Pointer$_old_#memory_$Pointer$.offset, write~$Pointer$_old_#memory_int := #memory_$Pointer$.base, #memory_$Pointer$.offset, #memory_int;
    write~$Pointer$_#value.base, write~$Pointer$_#ptr.offset, write~$Pointer$_#sizeOfWrittenType, write~$Pointer$_#value.offset, write~$Pointer$_#ptr.base := append_#t~ret14.base, append_~node~0.offset, 4, append_#t~ret14.offset, append_~node~0.base;
    assume 1 == #valid[write~$Pointer$_#ptr.base];
    assume write~$Pointer$_#ptr.offset + write~$Pointer$_#sizeOfWrittenType <= #length[write~$Pointer$_#ptr.base] && 0 <= write~$Pointer$_#ptr.offset;
    assume 1 == #valid[write~$Pointer$_#ptr.base];
    assume write~$Pointer$_#ptr.offset + write~$Pointer$_#sizeOfWrittenType <= #length[write~$Pointer$_#ptr.base] && 0 <= write~$Pointer$_#ptr.offset;
    havoc #memory_$Pointer$.base, #memory_$Pointer$.offset;
    assume (write~$Pointer$_old_#memory_int[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_int[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := #memory_int[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset]]] == #memory_int && #memory_$Pointer$.base == write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.base]]) && #memory_$Pointer$.offset == write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.offset]];
    havoc append_#t~ret14.offset, append_#t~ret14.base;
    write~$Pointer$_old_#memory_$Pointer$.base, write~$Pointer$_old_#memory_$Pointer$.offset, write~$Pointer$_old_#memory_int := #memory_$Pointer$.base, #memory_$Pointer$.offset, #memory_int;
    write~$Pointer$_#value.base, write~$Pointer$_#ptr.offset, write~$Pointer$_#sizeOfWrittenType, write~$Pointer$_#value.offset, write~$Pointer$_#ptr.base := append_~node~0.base, append_~pointerToList.offset, 4, append_~node~0.offset, append_~pointerToList.base;
    assume #valid[write~$Pointer$_#ptr.base] == 1;
    assume 0 <= write~$Pointer$_#ptr.offset && write~$Pointer$_#ptr.offset + write~$Pointer$_#sizeOfWrittenType <= #length[write~$Pointer$_#ptr.base];
    assume 1 == #valid[write~$Pointer$_#ptr.base];
    assume write~$Pointer$_#ptr.offset + write~$Pointer$_#sizeOfWrittenType <= #length[write~$Pointer$_#ptr.base] && 0 <= write~$Pointer$_#ptr.offset;
    havoc #memory_$Pointer$.base, #memory_$Pointer$.offset;
    assume (write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.offset]] == #memory_$Pointer$.offset && write~$Pointer$_old_#memory_int[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_int[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := #memory_int[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset]]] == #memory_int) && #memory_$Pointer$.base == write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.base]];
    assume 0 <= main_#t~nondet15 + 2147483648 && main_#t~nondet15 <= 2147483647;
    assume !(main_#t~nondet15 == 0);
    havoc main_#t~nondet15;
    goto loc1;
  loc3:
    assert false;
}

