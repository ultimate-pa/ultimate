var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var main_~#src~0.base : int;
    var read~int_#value : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~post2 : int;
    var write~int_#ptr.offset : int;
    var main_~#src~0.offset : int;
    var write~int_#ptr.base : int;
    var main_~#dst~0.base : int;
    var #Ultimate.alloc_#res.base : int;
    var main_~#dst~0.offset : int;
    var #Ultimate.alloc_#res.offset : int;
    var #Ultimate.alloc_~size : int;
    var main_~i~0 : int;
    var write~int_old_#memory_int : [int][int]int;
    var read~int_#sizeOfReadType : int;
    var main_old_#valid : [int]int;
    var main_~x~0 : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var write~int_#sizeOfWrittenType : int;
    var read~int_#ptr.base : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_#t~mem1 : int;
    var write~int_#value : int;
    var main_#t~mem0 : int;
    var main_#t~mem4 : int;
    var main_#t~mem3 : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_~#src~0.offset, main_~#dst~0.offset, main_~#src~0.base, main_#t~mem1, main_#t~post2, main_#t~mem0, main_~i~0, main_~#dst~0.base, main_~x~0, main_#t~mem4, main_#t~mem3;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 400000;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_~#src~0.offset, main_~#src~0.base := #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 400000;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #length == #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size];
    main_~#dst~0.offset, main_~#dst~0.base := #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    main_~i~0 := 0;
    goto loc1;
  loc1:
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := main_~#src~0.base, main_~#src~0.offset + 4 * main_~i~0, 4;
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
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    main_#t~mem0 := read~int_#value;
    assume !(main_#t~mem0 == 0);
    havoc main_#t~mem0;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := main_~#src~0.base, main_~#src~0.offset + 4 * main_~i~0, 4;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    main_#t~mem1 := read~int_#value;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, main_~#dst~0.base, main_#t~mem1, main_~#dst~0.offset + 4 * main_~i~0;
    assume 1 == #valid[write~int_#ptr.base];
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    assume #valid[write~int_#ptr.base] == 1;
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    havoc #memory_int;
    assume #memory_int == write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]];
    havoc main_#t~mem1;
    main_~i~0 := main_~i~0 + 1;
    goto loc1;
  loc3:
    assert false;
}

