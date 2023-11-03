var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var main_~arr~0.offset : int;
    var read~int_#value : int;
    var main_#t~nondet5 : int;
    var main_#t~nondet2 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~post6 : int;
    var write~int_#ptr.offset : int;
    var main_#t~post4 : int;
    var write~int_#ptr.base : int;
    var main_#t~malloc3.base : int;
    var main_~j~0 : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var #Ultimate.alloc_~size : int;
    var main_~i~0 : int;
    var write~int_old_#memory_int : [int][int]int;
    var read~int_#sizeOfReadType : int;
    var main_old_#valid : [int]int;
    var main_#t~malloc3.offset : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var main_#t~mem8 : int;
    var main_#t~post9 : int;
    var write~int_#sizeOfWrittenType : int;
    var main_#t~mem7 : int;
    var main_~arr~0.base : int;
    var read~int_#ptr.base : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_~val~0 : int;
    var write~int_#value : int;
    var main_~length~0 : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_~arr~0.offset, main_#t~nondet5, main_#t~nondet2, main_~i~0, main_#t~malloc3.offset, main_#t~post6, main_#t~post4, main_#t~mem8, main_#t~post9, main_#t~mem7, main_~arr~0.base, main_#t~malloc3.base, main_~j~0, main_~val~0, main_~length~0;
    havoc main_~i~0;
    havoc main_~j~0;
    havoc main_~val~0;
    assume 0 <= main_#t~nondet2 + 2147483648 && main_#t~nondet2 <= 2147483647;
    main_~length~0 := main_#t~nondet2;
    havoc main_#t~nondet2;
    assume !(536870911 <= main_~length~0) && !(main_~length~0 < 1);
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4 * main_~length~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc3.base, main_#t~malloc3.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~arr~0.offset, main_~arr~0.base := main_#t~malloc3.offset, main_#t~malloc3.base;
    assume !(0 == main_~arr~0.offset) || !(main_~arr~0.base == 0);
    main_~i~0 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~i~0 < main_~length~0);
    main_~j~0 := 0;
    goto loc3;
  loc2_1:
    assume main_~i~0 < main_~length~0;
    assume main_#t~nondet5 <= 2147483647 && 0 <= main_#t~nondet5 + 2147483648;
    main_~val~0 := main_#t~nondet5;
    havoc main_#t~nondet5;
    assume !(main_~val~0 < 0);
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, main_~arr~0.base, main_~val~0, main_~arr~0.offset + 4 * main_~i~0;
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    assume 1 == #valid[write~int_#ptr.base];
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    havoc #memory_int;
    assume #memory_int == write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]];
    main_#t~post4 := main_~i~0;
    main_~i~0 := main_#t~post4 + 1;
    havoc main_#t~post4;
    goto loc1;
  loc3:
    assume main_~j~0 < main_~length~0;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := main_~arr~0.base, main_~arr~0.offset + 4 * main_~j~0, 4;
    assume 1 == #valid[read~int_#ptr.base];
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume !(read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base]) || !(0 <= read~int_#ptr.offset);
    goto loc5;
  loc4_1:
    assume 0 <= read~int_#ptr.offset && read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base];
    assume 1 == #valid[read~int_#ptr.base];
    assume 0 <= read~int_#ptr.offset && read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base];
    havoc read~int_#value;
    assume read~int_#value == #memory_int[read~int_#ptr.base][read~int_#ptr.offset];
    main_#t~mem7 := read~int_#value;
    assume !(0 < main_#t~mem7);
    havoc main_#t~mem7;
    main_#t~post6 := main_~j~0;
    main_~j~0 := main_#t~post6 + 1;
    havoc main_#t~post6;
    goto loc3;
  loc5:
    assert false;
}

