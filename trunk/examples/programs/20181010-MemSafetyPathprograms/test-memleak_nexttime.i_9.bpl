var #memory_$Pointer$.base : [int][int]int;

var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var ~#a~0.base : int;

var #length : [int]int;

var ~#a~0.offset : int;

var #NULL.base : int;

var #memory_$Pointer$.offset : [int][int]int;

procedure ULTIMATE.start() returns ()
modifies #memory_$Pointer$.base, #valid, #memory_int, #NULL.offset, ~#a~0.base, #length, ~#a~0.offset, #NULL.base, #memory_$Pointer$.offset;
{
    var foo_~#p~0.offset : int;
    var #Ultimate.C_memcpy_dest.base : int;
    var foo_#t~malloc0.base : int;
    var write~$Pointer$_#sizeOfWrittenType : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var foo_#t~memcpy1.offset : int;
    var ULTIMATE.dealloc_~addr.offset : int;
    var write~unchecked~int_#sizeOfWrittenType : int;
    var main_~#p~1.base : int;
    var #Ultimate.C_memcpy_src.base : int;
    var foo_#t~memcpy1.base : int;
    var write~$Pointer$_old_#memory_int : [int][int]int;
    var write~$Pointer$_#value.offset : int;
    var ULTIMATE.dealloc_~addr.base : int;
    var write~unchecked~int_old_#memory_int : [int][int]int;
    var main_#t~mem3.offset : int;
    var write~unchecked~int_old_#memory_$Pointer$.offset : [int][int]int;
    var main_#t~mem3.base : int;
    var #Ultimate.C_memcpy_#res.base : int;
    var main_#t~memcpy2.offset : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var foo_~#p~0.base : int;
    var write~$Pointer$_old_#memory_$Pointer$.base : [int][int]int;
    var #Ultimate.C_memcpy_src.offset : int;
    var #Ultimate.alloc_~size : int;
    var main_~#p~1.offset : int;
    var #Ultimate.C_memcpy_dest.offset : int;
    var write~unchecked~int_old_#memory_$Pointer$.base : [int][int]int;
    var main_#t~memcpy2.base : int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var #Ultimate.C_memcpy_#res.offset : int;
    var write~unchecked~int_#ptr.base : int;
    var write~$Pointer$_#ptr.base : int;
    var ULTIMATE.dealloc_old_#valid : [int]int;
    var foo_#t~malloc0.offset : int;
    var write~$Pointer$_#value.base : int;
    var write~$Pointer$_#ptr.offset : int;
    var write~unchecked~int_#ptr.offset : int;
    var main_#res : int;
    var write~$Pointer$_old_#memory_$Pointer$.offset : [int][int]int;
    var #Ultimate.C_memcpy_size : int;
    var #Ultimate.C_memcpy_#t~loopctr5 : int;
    var write~unchecked~int_#value : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    ~#a~0.base, ~#a~0.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    write~unchecked~int_old_#memory_$Pointer$.base, write~unchecked~int_old_#memory_int, write~unchecked~int_old_#memory_$Pointer$.offset := #memory_$Pointer$.base, #memory_int, #memory_$Pointer$.offset;
    write~unchecked~int_#sizeOfWrittenType, write~unchecked~int_#ptr.offset, write~unchecked~int_#value, write~unchecked~int_#ptr.base := 1, ~#a~0.offset, 0, ~#a~0.base;
    havoc #memory_int;
    assume (write~unchecked~int_old_#memory_$Pointer$.base[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_$Pointer$.base[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := #memory_$Pointer$.base[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset]]] == #memory_$Pointer$.base && #memory_$Pointer$.offset == write~unchecked~int_old_#memory_$Pointer$.offset[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_$Pointer$.offset[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := #memory_$Pointer$.offset[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset]]]) && #memory_int == write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := write~unchecked~int_#value]];
    write~unchecked~int_old_#memory_$Pointer$.base, write~unchecked~int_old_#memory_int, write~unchecked~int_old_#memory_$Pointer$.offset := #memory_$Pointer$.base, #memory_int, #memory_$Pointer$.offset;
    write~unchecked~int_#sizeOfWrittenType, write~unchecked~int_#ptr.offset, write~unchecked~int_#value, write~unchecked~int_#ptr.base := 1, ~#a~0.offset + 1, 0, ~#a~0.base;
    havoc #memory_int;
    assume (#memory_int == write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := write~unchecked~int_#value]] && #memory_$Pointer$.offset == write~unchecked~int_old_#memory_$Pointer$.offset[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_$Pointer$.offset[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := #memory_$Pointer$.offset[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset]]]) && #memory_$Pointer$.base == write~unchecked~int_old_#memory_$Pointer$.base[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_$Pointer$.base[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := #memory_$Pointer$.base[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset]]];
    write~unchecked~int_old_#memory_$Pointer$.base, write~unchecked~int_old_#memory_int, write~unchecked~int_old_#memory_$Pointer$.offset := #memory_$Pointer$.base, #memory_int, #memory_$Pointer$.offset;
    write~unchecked~int_#sizeOfWrittenType, write~unchecked~int_#ptr.offset, write~unchecked~int_#value, write~unchecked~int_#ptr.base := 1, ~#a~0.offset + 2, 0, ~#a~0.base;
    havoc #memory_int;
    assume (write~unchecked~int_old_#memory_$Pointer$.base[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_$Pointer$.base[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := #memory_$Pointer$.base[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset]]] == #memory_$Pointer$.base && #memory_$Pointer$.offset == write~unchecked~int_old_#memory_$Pointer$.offset[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_$Pointer$.offset[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := #memory_$Pointer$.offset[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset]]]) && write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := write~unchecked~int_#value]] == #memory_int;
    write~unchecked~int_old_#memory_$Pointer$.base, write~unchecked~int_old_#memory_int, write~unchecked~int_old_#memory_$Pointer$.offset := #memory_$Pointer$.base, #memory_int, #memory_$Pointer$.offset;
    write~unchecked~int_#sizeOfWrittenType, write~unchecked~int_#ptr.offset, write~unchecked~int_#value, write~unchecked~int_#ptr.base := 1, ~#a~0.offset + 3, 0, ~#a~0.base;
    havoc #memory_int;
    assume (write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := write~unchecked~int_#value]] == #memory_int && write~unchecked~int_old_#memory_$Pointer$.base[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_$Pointer$.base[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := #memory_$Pointer$.base[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset]]] == #memory_$Pointer$.base) && write~unchecked~int_old_#memory_$Pointer$.offset[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_$Pointer$.offset[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := #memory_$Pointer$.offset[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset]]] == #memory_$Pointer$.offset;
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_~#p~1.base, main_~#p~1.offset, main_#t~memcpy2.base, main_#t~mem3.offset, main_#t~mem3.base, main_#t~memcpy2.offset;
    havoc foo_~#p~0.base, foo_~#p~0.offset, foo_#t~malloc0.offset, foo_#t~malloc0.base, foo_#t~memcpy1.base, foo_#t~memcpy1.offset;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #length == #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size];
    foo_~#p~0.base, foo_~#p~0.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 10;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    foo_#t~malloc0.offset, foo_#t~malloc0.base := #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    write~$Pointer$_old_#memory_$Pointer$.base, write~$Pointer$_old_#memory_$Pointer$.offset, write~$Pointer$_old_#memory_int := #memory_$Pointer$.base, #memory_$Pointer$.offset, #memory_int;
    write~$Pointer$_#value.base, write~$Pointer$_#ptr.offset, write~$Pointer$_#sizeOfWrittenType, write~$Pointer$_#value.offset, write~$Pointer$_#ptr.base := foo_#t~malloc0.base, foo_~#p~0.offset, 4, foo_#t~malloc0.offset, foo_~#p~0.base;
    assume 1 == #valid[write~$Pointer$_#ptr.base];
    assume 0 <= write~$Pointer$_#ptr.offset && write~$Pointer$_#sizeOfWrittenType + write~$Pointer$_#ptr.offset <= #length[write~$Pointer$_#ptr.base];
    assume 1 == #valid[write~$Pointer$_#ptr.base];
    assume write~$Pointer$_#sizeOfWrittenType + write~$Pointer$_#ptr.offset <= #length[write~$Pointer$_#ptr.base] && 0 <= write~$Pointer$_#ptr.offset;
    havoc #memory_$Pointer$.base, #memory_$Pointer$.offset;
    assume (#memory_int == write~$Pointer$_old_#memory_int[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_int[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := #memory_int[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset]]] && #memory_$Pointer$.base == write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.base[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.base]]) && #memory_$Pointer$.offset == write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base := write~$Pointer$_old_#memory_$Pointer$.offset[write~$Pointer$_#ptr.base][write~$Pointer$_#ptr.offset := write~$Pointer$_#value.offset]];
    #Ultimate.C_memcpy_src.base, #Ultimate.C_memcpy_src.offset, #Ultimate.C_memcpy_dest.base, #Ultimate.C_memcpy_dest.offset, #Ultimate.C_memcpy_size := foo_~#p~0.base, foo_~#p~0.offset, ~#a~0.base, ~#a~0.offset, 4;
    assume #valid[#Ultimate.C_memcpy_dest.base] == 1;
    assume 1 == #valid[#Ultimate.C_memcpy_src.base];
    assume #Ultimate.C_memcpy_size + #Ultimate.C_memcpy_dest.offset <= #length[#Ultimate.C_memcpy_dest.base] && 0 <= #Ultimate.C_memcpy_dest.offset;
    assume #Ultimate.C_memcpy_src.offset + #Ultimate.C_memcpy_size <= #length[#Ultimate.C_memcpy_src.base] && 0 <= #Ultimate.C_memcpy_src.offset;
    assume 1 == #valid[#Ultimate.C_memcpy_dest.base];
    assume #valid[#Ultimate.C_memcpy_src.base] == 1;
    assume #Ultimate.C_memcpy_dest.offset + #Ultimate.C_memcpy_size <= #length[#Ultimate.C_memcpy_dest.base] && 0 <= #Ultimate.C_memcpy_dest.offset;
    assume 0 <= #Ultimate.C_memcpy_src.offset && #Ultimate.C_memcpy_size + #Ultimate.C_memcpy_src.offset <= #length[#Ultimate.C_memcpy_src.base];
    havoc #Ultimate.C_memcpy_#res.base, #Ultimate.C_memcpy_#res.offset;
    havoc #Ultimate.C_memcpy_#t~loopctr5;
    #Ultimate.C_memcpy_#t~loopctr5 := 0;
    goto loc1;
  loc1:
    goto loc1_0, loc1_1;
  loc1_0:
    assume #Ultimate.C_memcpy_#t~loopctr5 < #Ultimate.C_memcpy_size;
    #memory_int := #memory_int[#Ultimate.C_memcpy_dest.base := #memory_int[#Ultimate.C_memcpy_dest.base][#Ultimate.C_memcpy_dest.offset + #Ultimate.C_memcpy_#t~loopctr5 := #memory_int[#Ultimate.C_memcpy_src.base][#Ultimate.C_memcpy_src.offset + #Ultimate.C_memcpy_#t~loopctr5]]];
    #memory_$Pointer$.base, #memory_$Pointer$.offset := #memory_$Pointer$.base[#Ultimate.C_memcpy_dest.base := #memory_$Pointer$.base[#Ultimate.C_memcpy_dest.base][#Ultimate.C_memcpy_dest.offset + #Ultimate.C_memcpy_#t~loopctr5 := #memory_$Pointer$.base[#Ultimate.C_memcpy_src.base][#Ultimate.C_memcpy_src.offset + #Ultimate.C_memcpy_#t~loopctr5]]], #memory_$Pointer$.offset[#Ultimate.C_memcpy_dest.base := #memory_$Pointer$.offset[#Ultimate.C_memcpy_dest.base][#Ultimate.C_memcpy_dest.offset + #Ultimate.C_memcpy_#t~loopctr5 := #memory_$Pointer$.offset[#Ultimate.C_memcpy_src.base][#Ultimate.C_memcpy_src.offset + #Ultimate.C_memcpy_#t~loopctr5]]];
    #Ultimate.C_memcpy_#t~loopctr5 := #Ultimate.C_memcpy_#t~loopctr5 + 1;
    goto loc1;
  loc1_1:
    assume !(#Ultimate.C_memcpy_#t~loopctr5 < #Ultimate.C_memcpy_size);
    assume #Ultimate.C_memcpy_#res.offset == #Ultimate.C_memcpy_dest.offset && #Ultimate.C_memcpy_dest.base == #Ultimate.C_memcpy_#res.base;
    foo_#t~memcpy1.base, foo_#t~memcpy1.offset := #Ultimate.C_memcpy_#res.base, #Ultimate.C_memcpy_#res.offset;
    havoc foo_#t~memcpy1.base, foo_#t~memcpy1.offset;
    ULTIMATE.dealloc_old_#valid := #valid;
    ULTIMATE.dealloc_~addr.base, ULTIMATE.dealloc_~addr.offset := foo_~#p~0.base, foo_~#p~0.offset;
    havoc #valid;
    assume #valid == ULTIMATE.dealloc_old_#valid[ULTIMATE.dealloc_~addr.base := 0];
    havoc foo_~#p~0.base, foo_~#p~0.offset;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base] == 0;
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume 0 == #Ultimate.alloc_#res.offset;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #length == #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size];
    main_~#p~1.base, main_~#p~1.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    #Ultimate.C_memcpy_src.base, #Ultimate.C_memcpy_src.offset, #Ultimate.C_memcpy_dest.base, #Ultimate.C_memcpy_dest.offset, #Ultimate.C_memcpy_size := ~#a~0.base, ~#a~0.offset, main_~#p~1.base, main_~#p~1.offset, 4;
    assume 1 == #valid[#Ultimate.C_memcpy_dest.base];
    assume !(#valid[#Ultimate.C_memcpy_src.base] == 1);
    goto loc2;
  loc2:
    assert false;
}

