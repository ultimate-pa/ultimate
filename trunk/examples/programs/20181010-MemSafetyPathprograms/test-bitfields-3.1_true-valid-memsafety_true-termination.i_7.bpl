var ~#d~0.offset : int;

var ~#d~0.base : int;

var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies ~#d~0.offset, ~#d~0.base, #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var #Ultimate.C_memcpy_dest.base : int;
    var main_#t~memcpy1.offset : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var write~unchecked~int_#sizeOfWrittenType : int;
    var main_#t~malloc0.base : int;
    var #Ultimate.C_memcpy_src.base : int;
    var write~unchecked~int_old_#memory_int : [int][int]int;
    var #Ultimate.C_memcpy_#res.base : int;
    var #Ultimate.alloc_#res.base : int;
    var main_#t~memcpy1.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var #Ultimate.C_memcpy_src.offset : int;
    var #Ultimate.alloc_~size : int;
    var #Ultimate.C_memcpy_dest.offset : int;
    var main_~p~0.base : int;
    var main_#t~malloc0.offset : int;
    var read~int_#sizeOfReadType : int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var main_~p~0.offset : int;
    var #Ultimate.C_memcpy_#res.offset : int;
    var write~unchecked~int_#ptr.base : int;
    var main_#t~mem7 : int;
    var read~int_#ptr.base : int;
    var write~unchecked~int_#ptr.offset : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_#t~mem2 : int;
    var #Ultimate.C_memcpy_size : int;
    var write~unchecked~int_#value : int;
    var main_#t~mem6 : int;
    var main_#t~mem5 : int;
    var main_#t~mem4 : int;
    var main_#t~mem3 : int;
    var #Ultimate.C_memcpy_#t~loopctr9 : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 10;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    ~#d~0.offset, ~#d~0.base := #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    write~unchecked~int_old_#memory_int := #memory_int;
    write~unchecked~int_#sizeOfWrittenType, write~unchecked~int_#ptr.offset, write~unchecked~int_#value, write~unchecked~int_#ptr.base := 1, ~#d~0.offset, 0, ~#d~0.base;
    havoc #memory_int;
    assume #memory_int == write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := write~unchecked~int_#value]];
    write~unchecked~int_old_#memory_int := #memory_int;
    write~unchecked~int_#sizeOfWrittenType, write~unchecked~int_#ptr.offset, write~unchecked~int_#value, write~unchecked~int_#ptr.base := 1, ~#d~0.offset + 1, 2, ~#d~0.base;
    havoc #memory_int;
    assume #memory_int == write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := write~unchecked~int_#value]];
    write~unchecked~int_old_#memory_int := #memory_int;
    write~unchecked~int_#sizeOfWrittenType, write~unchecked~int_#ptr.offset, write~unchecked~int_#value, write~unchecked~int_#ptr.base := 1, ~#d~0.offset + 2, 3, ~#d~0.base;
    havoc #memory_int;
    assume write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := write~unchecked~int_#value]] == #memory_int;
    write~unchecked~int_old_#memory_int := #memory_int;
    write~unchecked~int_#sizeOfWrittenType, write~unchecked~int_#ptr.offset, write~unchecked~int_#value, write~unchecked~int_#ptr.base := 1, ~#d~0.offset + 3, 4, ~#d~0.base;
    havoc #memory_int;
    assume write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := write~unchecked~int_#value]] == #memory_int;
    write~unchecked~int_old_#memory_int := #memory_int;
    write~unchecked~int_#sizeOfWrittenType, write~unchecked~int_#ptr.offset, write~unchecked~int_#value, write~unchecked~int_#ptr.base := 1, ~#d~0.offset + 4, 0, ~#d~0.base;
    havoc #memory_int;
    assume write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := write~unchecked~int_#value]] == #memory_int;
    write~unchecked~int_old_#memory_int := #memory_int;
    write~unchecked~int_#sizeOfWrittenType, write~unchecked~int_#ptr.offset, write~unchecked~int_#value, write~unchecked~int_#ptr.base := 1, ~#d~0.offset + 5, 0, ~#d~0.base;
    havoc #memory_int;
    assume write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := write~unchecked~int_#value]] == #memory_int;
    write~unchecked~int_old_#memory_int := #memory_int;
    write~unchecked~int_#sizeOfWrittenType, write~unchecked~int_#ptr.offset, write~unchecked~int_#value, write~unchecked~int_#ptr.base := 1, ~#d~0.offset + 6, 0, ~#d~0.base;
    havoc #memory_int;
    assume write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := write~unchecked~int_#value]] == #memory_int;
    write~unchecked~int_old_#memory_int := #memory_int;
    write~unchecked~int_#sizeOfWrittenType, write~unchecked~int_#ptr.offset, write~unchecked~int_#value, write~unchecked~int_#ptr.base := 1, ~#d~0.offset + 7, 0, ~#d~0.base;
    havoc #memory_int;
    assume write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := write~unchecked~int_#value]] == #memory_int;
    write~unchecked~int_old_#memory_int := #memory_int;
    write~unchecked~int_#sizeOfWrittenType, write~unchecked~int_#ptr.offset, write~unchecked~int_#value, write~unchecked~int_#ptr.base := 1, ~#d~0.offset + 8, 0, ~#d~0.base;
    havoc #memory_int;
    assume write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := write~unchecked~int_#value]] == #memory_int;
    write~unchecked~int_old_#memory_int := #memory_int;
    write~unchecked~int_#sizeOfWrittenType, write~unchecked~int_#ptr.offset, write~unchecked~int_#value, write~unchecked~int_#ptr.base := 1, ~#d~0.offset + 9, 0, ~#d~0.base;
    havoc #memory_int;
    assume write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base := write~unchecked~int_old_#memory_int[write~unchecked~int_#ptr.base][write~unchecked~int_#ptr.offset := write~unchecked~int_#value]] == #memory_int;
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~memcpy1.base, main_#t~malloc0.base, main_#t~mem7, main_#t~memcpy1.offset, main_#t~mem2, main_~p~0.base, main_#t~malloc0.offset, main_#t~mem6, main_#t~mem5, main_#t~mem4, main_~p~0.offset, main_#t~mem3;
    havoc main_~p~0.base, main_~p~0.offset;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 10;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #length == #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size];
    main_#t~malloc0.base, main_#t~malloc0.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~p~0.base, main_~p~0.offset := main_#t~malloc0.base, main_#t~malloc0.offset;
    #Ultimate.C_memcpy_src.base, #Ultimate.C_memcpy_src.offset, #Ultimate.C_memcpy_dest.base, #Ultimate.C_memcpy_dest.offset, #Ultimate.C_memcpy_size := ~#d~0.base, ~#d~0.offset, main_~p~0.base, main_~p~0.offset, 10;
    assume 1 == #valid[#Ultimate.C_memcpy_dest.base];
    assume 1 == #valid[#Ultimate.C_memcpy_src.base];
    assume #Ultimate.C_memcpy_size + #Ultimate.C_memcpy_dest.offset <= #length[#Ultimate.C_memcpy_dest.base] && 0 <= #Ultimate.C_memcpy_dest.offset;
    assume #Ultimate.C_memcpy_src.offset + #Ultimate.C_memcpy_size <= #length[#Ultimate.C_memcpy_src.base] && 0 <= #Ultimate.C_memcpy_src.offset;
    assume 1 == #valid[#Ultimate.C_memcpy_dest.base];
    assume #valid[#Ultimate.C_memcpy_src.base] == 1;
    assume 0 <= #Ultimate.C_memcpy_dest.offset && #Ultimate.C_memcpy_dest.offset + #Ultimate.C_memcpy_size <= #length[#Ultimate.C_memcpy_dest.base];
    assume 0 <= #Ultimate.C_memcpy_src.offset && #Ultimate.C_memcpy_size + #Ultimate.C_memcpy_src.offset <= #length[#Ultimate.C_memcpy_src.base];
    havoc #Ultimate.C_memcpy_#res.base, #Ultimate.C_memcpy_#res.offset;
    havoc #Ultimate.C_memcpy_#t~loopctr9;
    #Ultimate.C_memcpy_#t~loopctr9 := 0;
    goto loc1;
  loc1:
    goto loc1_0, loc1_1;
  loc1_0:
    assume #Ultimate.C_memcpy_#t~loopctr9 < #Ultimate.C_memcpy_size;
    #memory_int := #memory_int[#Ultimate.C_memcpy_dest.base := #memory_int[#Ultimate.C_memcpy_dest.base][#Ultimate.C_memcpy_#t~loopctr9 + #Ultimate.C_memcpy_dest.offset := #memory_int[#Ultimate.C_memcpy_src.base][#Ultimate.C_memcpy_#t~loopctr9 + #Ultimate.C_memcpy_src.offset]]];
    #Ultimate.C_memcpy_#t~loopctr9 := #Ultimate.C_memcpy_#t~loopctr9 + 1;
    goto loc1;
  loc1_1:
    assume !(#Ultimate.C_memcpy_#t~loopctr9 < #Ultimate.C_memcpy_size);
    assume #Ultimate.C_memcpy_dest.base == #Ultimate.C_memcpy_#res.base && #Ultimate.C_memcpy_#res.offset == #Ultimate.C_memcpy_dest.offset;
    main_#t~memcpy1.base, main_#t~memcpy1.offset := #Ultimate.C_memcpy_#res.base, #Ultimate.C_memcpy_#res.offset;
    havoc main_#t~memcpy1.base, main_#t~memcpy1.offset;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := main_~p~0.base, main_~p~0.offset, 1;
    assume 1 == #valid[read~int_#ptr.base];
    assume !(read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base]) || !(0 <= read~int_#ptr.offset);
    goto loc2;
  loc2:
    assert false;
}

