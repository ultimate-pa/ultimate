var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var main_#t~nondet0 : int;
    var #Ultimate.alloc_#res.offset : int;
    var read~int_#value : int;
    var #Ultimate.alloc_~size : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~post1 : int;
    var main_~i~0 : int;
    var main_~#array~0.offset : int;
    var read~int_#sizeOfReadType : int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var main_#t~post4 : int;
    var main_~#array~0.base : int;
    var read~int_#ptr.base : int;
    var main_~num~0 : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_#t~mem2 : int;
    var main_#t~mem6 : int;
    var main_#t~mem5 : int;
    var main_#t~mem3 : int;
    var #Ultimate.alloc_#res.base : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~nondet0, main_~#array~0.base, main_~num~0, main_#t~mem2, main_#t~post1, main_~i~0, main_~#array~0.offset, main_#t~mem6, main_#t~mem5, main_#t~mem3, main_#t~post4;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 400000;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_~#array~0.base, main_~#array~0.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    havoc main_~i~0;
    assume 0 <= main_#t~nondet0 + 2147483648 && main_#t~nondet0 <= 2147483647;
    main_~num~0 := main_#t~nondet0;
    havoc main_#t~nondet0;
    main_~i~0 := 0;
    goto loc1;
  loc1:
    assume main_~i~0 < main_~num~0;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := main_~#array~0.base, main_~#array~0.offset + 4 * main_~i~0, 4;
    assume 1 == #valid[read~int_#ptr.base];
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base]) || !(0 <= read~int_#ptr.offset);
    goto loc3;
  loc2_1:
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume #valid[read~int_#ptr.base] == 1;
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    main_#t~mem2 := read~int_#value;
    assume !((if !(main_#t~mem2 % 2 == 0) && main_#t~mem2 < 0 then main_#t~mem2 % 2 + -2 else main_#t~mem2 % 2) == 0);
    havoc main_#t~mem2;
    main_#t~post1 := main_~i~0;
    main_~i~0 := main_#t~post1 + 1;
    havoc main_#t~post1;
    goto loc1;
  loc3:
    assert false;
}

