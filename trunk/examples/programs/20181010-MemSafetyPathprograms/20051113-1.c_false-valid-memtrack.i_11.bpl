var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var #Ultimate.C_memset_#amount : int;
    var main_#t~malloc11.offset : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~malloc11.base : int;
    var main_#t~memset12.offset : int;
    var write~int_#ptr.offset : int;
    var #Ultimate.C_memset_#ptr.offset : int;
    var write~int_#ptr.base : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var #Ultimate.alloc_~size : int;
    var main_#t~memset12.base : int;
    var main_~p~0.base : int;
    var write~int_old_#memory_int : [int][int]int;
    var main_old_#valid : [int]int;
    var main_~p~0.offset : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var #Ultimate.C_memset_#t~loopctr16 : int;
    var main_#t~ret14 : int;
    var write~int_#sizeOfWrittenType : int;
    var #Ultimate.C_memset_#value : int;
    var main_#t~ret13 : int;
    var main_#res : int;
    var #Ultimate.C_memset_#ptr.base : int;
    var #Ultimate.C_memset_#res.base : int;
    var #Ultimate.C_memset_#res.offset : int;
    var write~int_#value : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~ret14, main_#t~ret13, main_#t~malloc11.offset, main_#t~memset12.base, main_~p~0.base, main_#t~malloc11.base, main_#t~memset12.offset, main_~p~0.offset;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 94;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc11.offset, main_#t~malloc11.base := #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    main_~p~0.base, main_~p~0.offset := main_#t~malloc11.base, main_#t~malloc11.offset;
    #Ultimate.C_memset_#ptr.offset, #Ultimate.C_memset_#value, #Ultimate.C_memset_#amount, #Ultimate.C_memset_#ptr.base := main_~p~0.offset, 0, 94, main_~p~0.base;
    assume #valid[#Ultimate.C_memset_#ptr.base] == 1;
    assume 0 <= #Ultimate.C_memset_#ptr.offset && #Ultimate.C_memset_#ptr.offset + #Ultimate.C_memset_#amount <= #length[#Ultimate.C_memset_#ptr.base];
    assume #valid[#Ultimate.C_memset_#ptr.base] == 1;
    assume 0 <= #Ultimate.C_memset_#ptr.offset && #Ultimate.C_memset_#amount + #Ultimate.C_memset_#ptr.offset <= #length[#Ultimate.C_memset_#ptr.base];
    havoc #Ultimate.C_memset_#res.base, #Ultimate.C_memset_#res.offset;
    havoc #Ultimate.C_memset_#t~loopctr16;
    #Ultimate.C_memset_#t~loopctr16 := 0;
    goto loc1;
  loc1:
    goto loc1_0, loc1_1;
  loc1_0:
    assume #Ultimate.C_memset_#t~loopctr16 < #Ultimate.C_memset_#amount;
    #memory_int := #memory_int[#Ultimate.C_memset_#ptr.base := #memory_int[#Ultimate.C_memset_#ptr.base][#Ultimate.C_memset_#t~loopctr16 + #Ultimate.C_memset_#ptr.offset := #Ultimate.C_memset_#value]];
    #Ultimate.C_memset_#t~loopctr16 := #Ultimate.C_memset_#t~loopctr16 + 1;
    goto loc1;
  loc1_1:
    assume !(#Ultimate.C_memset_#t~loopctr16 < #Ultimate.C_memset_#amount);
    assume #Ultimate.C_memset_#ptr.offset == #Ultimate.C_memset_#res.offset && #Ultimate.C_memset_#ptr.base == #Ultimate.C_memset_#res.base;
    main_#t~memset12.base, main_#t~memset12.offset := #Ultimate.C_memset_#res.base, #Ultimate.C_memset_#res.offset;
    havoc main_#t~memset12.base, main_#t~memset12.offset;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, main_~p~0.base, 3, main_~p~0.offset;
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    assume 1 == #valid[write~int_#ptr.base];
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    havoc #memory_int;
    assume #memory_int == write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]];
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 8, main_~p~0.base, 555, main_~p~0.offset + 10;
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#ptr.offset + write~int_#sizeOfWrittenType <= #length[write~int_#ptr.base];
    assume #valid[write~int_#ptr.base] == 1;
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    havoc #memory_int;
    assume write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]] == #memory_int;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 8, main_~p~0.base, 999, main_~p~0.offset + 40;
    assume 1 == #valid[write~int_#ptr.base];
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    assume 1 == #valid[write~int_#ptr.base];
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    havoc #memory_int;
    assume write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]] == #memory_int;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 8, main_~p~0.base, 4311810305, main_~p~0.offset + 70;
    assume 1 == #valid[write~int_#ptr.base];
    assume !(0 <= write~int_#ptr.offset) || !(write~int_#ptr.offset + write~int_#sizeOfWrittenType <= #length[write~int_#ptr.base]);
    goto loc2;
  loc2:
    assert false;
}

