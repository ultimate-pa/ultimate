var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var main_#t~malloc4.offset : int;
    var main_~arr~0.offset : int;
    var read~int_#value : int;
    var main_#t~nondet2 : int;
    var main_#t~post3 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~post5 : int;
    var main_~j~0 : int;
    var main_#t~short11 : bool;
    var main_#t~post15.offset : int;
    var #Ultimate.alloc_#res.base : int;
    var main_#t~mem10 : int;
    var #Ultimate.alloc_#res.offset : int;
    var main_#t~mem12 : int;
    var main_#t~mem13 : int;
    var main_~tmp~0 : int;
    var #Ultimate.alloc_~size : int;
    var main_~b~0.offset : int;
    var main_#t~malloc4.base : int;
    var main_#t~post14.offset : int;
    var main_~i~0 : int;
    var read~int_#sizeOfReadType : int;
    var main_old_#valid : [int]int;
    var main_~a~0.base : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var main_#t~post14.base : int;
    var main_#t~post15.base : int;
    var main_#t~mem9 : int;
    var main_#t~mem7 : int;
    var main_#t~post8 : int;
    var main_~arr~0.base : int;
    var read~int_#ptr.base : int;
    var main_~a~0.offset : int;
    var main_~b~0.base : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_#t~mem6 : int;
    var main_~length~0 : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~malloc4.offset, main_~arr~0.offset, main_#t~nondet2, main_#t~post3, main_#t~post5, main_~j~0, main_#t~short11, main_#t~post15.offset, main_#t~mem10, main_#t~mem12, main_#t~mem13, main_~tmp~0, main_~b~0.offset, main_#t~malloc4.base, main_#t~post14.offset, main_~i~0, main_~a~0.base, main_#t~post14.base, main_#t~post15.base, main_#t~mem9, main_#t~mem7, main_#t~post8, main_~arr~0.base, main_~a~0.offset, main_~b~0.base, main_#t~mem6, main_~length~0;
    havoc main_~i~0;
    havoc main_~j~0;
    havoc main_~tmp~0;
    assume 0 <= main_#t~nondet2 + 2147483648 && main_#t~nondet2 <= 2147483647;
    main_~length~0 := main_#t~nondet2;
    havoc main_#t~nondet2;
    assume !(main_~length~0 < 1);
    assume !((if !(main_~length~0 % 2 == 0) && main_~length~0 < 0 then main_~length~0 % 2 + -2 else main_~length~0 % 2) == 0);
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4 * main_~length~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc4.offset, main_#t~malloc4.base := #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    main_~arr~0.offset, main_~arr~0.base := main_#t~malloc4.offset, main_#t~malloc4.base;
    main_~i~0 := 0;
    goto loc1;
  loc1:
    assume main_~i~0 < main_~length~0;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := main_~arr~0.base, main_~arr~0.offset + 4 * main_~i~0, 4;
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
    main_#t~mem6 := read~int_#value;
    assume !(main_#t~mem6 == 0);
    havoc main_#t~mem6;
    main_#t~post5 := main_~i~0;
    main_~i~0 := main_#t~post5 + 1;
    havoc main_#t~post5;
    goto loc1;
  loc3:
    assert false;
}

