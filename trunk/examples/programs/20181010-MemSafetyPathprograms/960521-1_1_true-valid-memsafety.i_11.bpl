var ~b~0.base : int;

var ~a~0.base : int;

var #valid : [int]int;

var ~b~0.offset : int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var ~a~0.offset : int;

var #length : [int]int;

var ~n~0 : int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies ~b~0.base, ~a~0.base, #valid, ~b~0.offset, #memory_int, #NULL.offset, ~a~0.offset, #length, ~n~0, #NULL.base;
{
    var main_#t~malloc4.offset : int;
    var main_#t~nondet2 : int;
    var main_#t~post3 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var write~int_#ptr.offset : int;
    var main_#t~post6.base : int;
    var foo_#t~post1 : int;
    var write~int_#ptr.base : int;
    var foo_#t~post0 : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var #Ultimate.alloc_~size : int;
    var foo_~i~0 : int;
    var main_#t~malloc4.base : int;
    var main_#t~malloc5.base : int;
    var write~int_old_#memory_int : [int][int]int;
    var main_old_#valid : [int]int;
    var main_#t~post6.offset : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var main_#t~mem8 : int;
    var write~int_#sizeOfWrittenType : int;
    var main_#t~mem7 : int;
    var main_#res : int;
    var write~int_#value : int;
    var main_#t~malloc5.offset : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    ~a~0.base, ~a~0.offset := 0, 0;
    ~b~0.base, ~b~0.offset := 0, 0;
    ~n~0 := 0;
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~malloc4.offset, main_#t~post6.base, main_#t~mem8, main_#t~mem7, main_#t~nondet2, main_#t~post3, main_#t~malloc4.base, main_#t~malloc5.base, main_#t~post6.offset, main_#t~malloc5.offset;
    ~n~0 := 1;
    goto loc1;
  loc1:
    assume 0 <= main_#t~nondet2 + 2147483648 && main_#t~nondet2 <= 2147483647;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(~n~0 < 30) || 0 == main_#t~nondet2;
    havoc main_#t~nondet2;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4 * ~n~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc4.offset, main_#t~malloc4.base := #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    ~a~0.base, ~a~0.offset := main_#t~malloc4.base, main_#t~malloc4.offset;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4 * ~n~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #length == #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size];
    main_#t~malloc5.base, main_#t~malloc5.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    ~b~0.base, ~b~0.offset := main_#t~malloc5.base, main_#t~malloc5.offset;
    main_#t~post6.base, main_#t~post6.offset := ~b~0.base, ~b~0.offset;
    ~b~0.base, ~b~0.offset := main_#t~post6.base, main_#t~post6.offset + 4;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, main_#t~post6.base, ~n~0, main_#t~post6.offset;
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    assume 1 == #valid[write~int_#ptr.base];
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    havoc #memory_int;
    assume #memory_int == write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]];
    havoc main_#t~post6.base, main_#t~post6.offset;
    havoc foo_#t~post1, foo_#t~post0, foo_~i~0;
    havoc foo_~i~0;
    foo_~i~0 := 0;
    goto loc3;
  loc2_1:
    assume ~n~0 < 30 && !(0 == main_#t~nondet2);
    havoc main_#t~nondet2;
    main_#t~post3 := ~n~0;
    ~n~0 := main_#t~post3 + 1;
    havoc main_#t~post3;
    goto loc1;
  loc3:
    assume foo_~i~0 < ~n~0;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, ~a~0.base, ~n~0, ~a~0.offset + 4 * foo_~i~0;
    assume #valid[write~int_#ptr.base] == 1;
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume !(write~int_#ptr.offset + write~int_#sizeOfWrittenType <= #length[write~int_#ptr.base]) || !(0 <= write~int_#ptr.offset);
    goto loc5;
  loc4_1:
    assume 0 <= write~int_#ptr.offset && write~int_#ptr.offset + write~int_#sizeOfWrittenType <= #length[write~int_#ptr.base];
    assume #valid[write~int_#ptr.base] == 1;
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    havoc #memory_int;
    assume write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]] == #memory_int;
    foo_#t~post0 := foo_~i~0;
    foo_~i~0 := foo_#t~post0 + 1;
    havoc foo_#t~post0;
    goto loc3;
  loc5:
    assert false;
}

