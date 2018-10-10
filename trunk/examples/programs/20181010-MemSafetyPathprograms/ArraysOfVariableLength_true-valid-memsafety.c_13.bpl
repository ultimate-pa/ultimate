var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var foo_#in~size : int;
    var read~int_#value : int;
    var foo_#t~mem1 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~post2 : int;
    var foo_#res : int;
    var foo_~size : int;
    var foo_#in~n : int;
    var write~int_#ptr.offset : int;
    var main_#t~post4 : int;
    var foo_~a~0 : [int]int;
    var foo_~n : int;
    var foo_#t~post0 : int;
    var write~int_#ptr.base : int;
    var main_~#b~0.base : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var foo_#in~b.offset : int;
    var #Ultimate.alloc_~size : int;
    var foo_~i~0 : int;
    var foo_~b.offset : int;
    var write~int_old_#memory_int : [int][int]int;
    var main_~i~1 : int;
    var read~int_#sizeOfReadType : int;
    var main_old_#valid : [int]int;
    var foo_#in~b.base : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var write~int_#sizeOfWrittenType : int;
    var read~int_#ptr.base : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var write~int_#value : int;
    var foo_~b.base : int;
    var main_~#b~0.offset : int;
    var main_#t~mem5 : int;
    var main_#t~ret3 : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~post2, main_~#b~0.base, main_~i~1, main_~#b~0.offset, main_#t~mem5, main_#t~ret3, main_#t~post4;
    havoc main_~i~1;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 400;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_~#b~0.base, main_~#b~0.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~i~1 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~i~1 < 100);
    main_~i~1 := 0;
    goto loc3;
  loc2_1:
    assume main_~i~1 < 100;
    foo_#in~b.offset, foo_#in~size, foo_#in~b.base, foo_#in~n := main_~#b~0.offset, main_~i~1, main_~#b~0.base, main_~i~1;
    havoc foo_#res;
    havoc foo_~n, foo_#t~post0, foo_#t~mem1, foo_~i~0, foo_~b.offset, foo_~b.base, foo_~size, foo_~a~0;
    foo_~n := foo_#in~n;
    foo_~b.offset, foo_~b.base := foo_#in~b.offset, foo_#in~b.base;
    foo_~size := foo_#in~size;
    havoc foo_~a~0;
    havoc foo_~i~0;
    foo_~i~0 := 0;
    goto loc4;
  loc3:
    assume main_~i~1 < 100;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := main_~#b~0.base, main_~#b~0.offset + 4 * main_~i~1, 4;
    assume 1 == #valid[read~int_#ptr.base];
    goto loc5;
  loc4:
    goto loc6;
  loc5:
    goto loc5_0, loc5_1;
  loc5_0:
    assume !(read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base]) || !(0 <= read~int_#ptr.offset);
    goto loc7;
  loc5_1:
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    main_#t~mem5 := read~int_#value;
    assume main_#t~mem5 == main_~i~1;
    havoc main_#t~mem5;
    main_#t~post4 := main_~i~1;
    main_~i~1 := main_#t~post4 + 1;
    havoc main_#t~post4;
    goto loc3;
  loc6:
    goto loc6_0, loc6_1;
  loc6_0:
    assume !(foo_~i~0 < foo_~size);
    foo_#res := foo_~i~0;
    main_#t~ret3 := foo_#res;
    assume 0 <= main_#t~ret3 + 2147483648 && main_#t~ret3 <= 2147483647;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, main_~#b~0.base, main_#t~ret3, main_~#b~0.offset + 4 * main_~i~1;
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    assume 1 == #valid[write~int_#ptr.base];
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    havoc #memory_int;
    assume #memory_int == write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]];
    havoc main_#t~ret3;
    main_#t~post2 := main_~i~1;
    main_~i~1 := main_#t~post2 + 1;
    havoc main_#t~post2;
    goto loc1;
  loc6_1:
    assume foo_~i~0 < foo_~size;
    assume foo_~i~0 < foo_~n && 0 <= foo_~i~0;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := foo_~b.base, 4 * foo_~i~0 + foo_~b.offset, 4;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume #valid[read~int_#ptr.base] == 1;
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    foo_#t~mem1 := read~int_#value;
    foo_~a~0 := foo_~a~0[foo_~i~0 := foo_#t~mem1];
    havoc foo_#t~mem1;
    foo_#t~post0 := foo_~i~0;
    foo_~i~0 := foo_#t~post0 + 1;
    havoc foo_#t~post0;
    goto loc4;
  loc7:
    assert false;
}

