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
    var bar_~b.base : int;
    var foo_#res : int;
    var write~int_#ptr.base : int;
    var ULTIMATE.dealloc_~addr.base : int;
    var foo_~#a~0.offset : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var foo_#in~b.offset : int;
    var foo_~i~1 : int;
    var bar_#t~mem1 : int;
    var foo_~b.offset : int;
    var write~int_old_#memory_int : [int][int]int;
    var main_old_#valid : [int]int;
    var foo_#in~b.base : int;
    var bar_~res~0 : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var ULTIMATE.dealloc_old_#valid : [int]int;
    var write~int_#sizeOfWrittenType : int;
    var main_#t~mem7 : int;
    var foo_#t~ret4 : int;
    var bar_~size : int;
    var read~int_#ptr.base : int;
    var write~int_#value : int;
    var foo_~b.base : int;
    var foo_#t~mem3 : int;
    var bar_~i~0 : int;
    var main_~#b~0.offset : int;
    var main_#t~ret6 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var foo_~size : int;
    var bar_#t~post0 : int;
    var main_#t~post5 : int;
    var foo_#in~n : int;
    var write~int_#ptr.offset : int;
    var ULTIMATE.dealloc_~addr.offset : int;
    var foo_~n : int;
    var foo_#t~post2 : int;
    var bar_#in~b.offset : int;
    var bar_~b.offset : int;
    var bar_#res : int;
    var main_~#b~0.base : int;
    var bar_#in~size : int;
    var #Ultimate.alloc_~size : int;
    var bar_#in~b.base : int;
    var foo_~#a~0.base : int;
    var read~int_#sizeOfReadType : int;
    var main_~i~2 : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~mem7, main_~#b~0.base, main_~i~2, main_~#b~0.offset, main_#t~ret6, main_#t~post5;
    havoc main_~i~2;
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
    main_~i~2 := 0;
    goto loc1;
  loc1:
    assume main_~i~2 < 100;
    foo_#in~b.offset, foo_#in~size, foo_#in~b.base, foo_#in~n := main_~#b~0.offset, main_~i~2, main_~#b~0.base, main_~i~2;
    havoc foo_#res;
    havoc foo_~n, foo_#t~post2, foo_#t~ret4, foo_~i~1, foo_~#a~0.base, foo_~b.offset, foo_~b.base, foo_~size, foo_#t~mem3, foo_~#a~0.offset;
    foo_~n := foo_#in~n;
    foo_~b.offset, foo_~b.base := foo_#in~b.offset, foo_#in~b.base;
    foo_~size := foo_#in~size;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4 * foo_~n;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #length == #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size];
    foo_~#a~0.base, foo_~#a~0.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    havoc foo_~i~1;
    foo_~i~1 := 0;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(foo_~i~1 < foo_~size);
    bar_#in~size, bar_#in~b.offset, bar_#in~b.base := foo_~size, foo_~#a~0.offset, foo_~#a~0.base;
    havoc bar_#res;
    havoc bar_~b.offset, bar_~size, bar_#t~mem1, bar_~b.base, bar_~i~0, bar_#t~post0, bar_~res~0;
    bar_~b.offset, bar_~b.base := bar_#in~b.offset, bar_#in~b.base;
    bar_~size := bar_#in~size;
    bar_~res~0 := 0;
    havoc bar_~i~0;
    bar_~i~0 := 0;
    assume !(bar_~i~0 < bar_~size);
    bar_#res := bar_~res~0;
    foo_#t~ret4 := bar_#res;
    assume foo_#t~ret4 <= 2147483647 && 0 <= foo_#t~ret4 + 2147483648;
    assume 0 == foo_#t~ret4;
    havoc foo_#t~ret4;
    foo_#res := foo_~i~1;
    ULTIMATE.dealloc_old_#valid := #valid;
    ULTIMATE.dealloc_~addr.base, ULTIMATE.dealloc_~addr.offset := foo_~#a~0.base, foo_~#a~0.offset;
    havoc #valid;
    assume #valid == ULTIMATE.dealloc_old_#valid[ULTIMATE.dealloc_~addr.base := 0];
    havoc foo_~#a~0.base, foo_~#a~0.offset;
    main_#t~ret6 := foo_#res;
    assume main_#t~ret6 <= 2147483647 && 0 <= main_#t~ret6 + 2147483648;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, main_~#b~0.base, main_#t~ret6, main_~#b~0.offset + 4 * main_~i~2;
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#ptr.offset + write~int_#sizeOfWrittenType <= #length[write~int_#ptr.base];
    assume 1 == #valid[write~int_#ptr.base];
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    havoc #memory_int;
    assume write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]] == #memory_int;
    havoc main_#t~ret6;
    main_#t~post5 := main_~i~2;
    main_~i~2 := main_#t~post5 + 1;
    havoc main_#t~post5;
    goto loc1;
  loc2_1:
    assume foo_~i~1 < foo_~size;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := foo_~b.base, 4 * foo_~i~1 + foo_~b.offset, 4;
    assume 1 == #valid[read~int_#ptr.base];
    assume 0 <= read~int_#ptr.offset && read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base];
    assume #valid[read~int_#ptr.base] == 1;
    assume 0 <= read~int_#ptr.offset && read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base];
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    foo_#t~mem3 := read~int_#value;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, foo_~#a~0.base, foo_#t~mem3, 4 * foo_~i~1 + foo_~#a~0.offset;
    assume 1 == #valid[write~int_#ptr.base];
    assume !(write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base]) || !(0 <= write~int_#ptr.offset);
    goto loc3;
  loc3:
    assert false;
}

