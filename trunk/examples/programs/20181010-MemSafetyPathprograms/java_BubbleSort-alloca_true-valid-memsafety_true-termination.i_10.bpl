var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var read~int_#value : int;
    var sort_~i~0 : int;
    var main_#t~nondet8 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var sort_#t~post2 : int;
    var sort_#in~x.base : int;
    var sort_#t~post3 : int;
    var sort_~temp~0 : int;
    var main_~numbers~0.base : int;
    var sort_#t~mem5 : int;
    var sort_#t~mem4 : int;
    var main_#t~malloc9.offset : int;
    var sort_~x.base : int;
    var sort_#t~mem7 : int;
    var #Ultimate.alloc_#res.base : int;
    var sort_#t~mem6 : int;
    var #Ultimate.alloc_#res.offset : int;
    var main_#t~malloc9.base : int;
    var #Ultimate.alloc_~size : int;
    var sort_~x.offset : int;
    var sort_~pass~0 : int;
    var read~int_#sizeOfReadType : int;
    var main_old_#valid : [int]int;
    var sort_#in~n : int;
    var sort_~n : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var read~int_#ptr.base : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_~array_size~0 : int;
    var main_~numbers~0.offset : int;
    var sort_#in~x.offset : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~malloc9.base, main_~array_size~0, main_~numbers~0.base, main_#t~nondet8, main_~numbers~0.offset, main_#t~malloc9.offset;
    assume 0 <= main_#t~nondet8 + 2147483648 && main_#t~nondet8 <= 2147483647;
    main_~array_size~0 := main_#t~nondet8;
    havoc main_#t~nondet8;
    assume !(main_~array_size~0 < 1) && !(536870911 <= main_~array_size~0);
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4 * main_~array_size~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc9.base, main_#t~malloc9.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~numbers~0.base, main_~numbers~0.offset := main_#t~malloc9.base, main_#t~malloc9.offset;
    sort_#in~x.base, sort_#in~n, sort_#in~x.offset := main_~numbers~0.base, main_~array_size~0, main_~numbers~0.offset;
    havoc sort_~x.offset, sort_~i~0, sort_#t~mem5, sort_#t~post2, sort_~pass~0, sort_#t~mem4, sort_#t~post3, sort_~n, sort_~x.base, sort_#t~mem7, sort_#t~mem6, sort_~temp~0;
    sort_~x.offset, sort_~x.base := sort_#in~x.offset, sort_#in~x.base;
    sort_~n := sort_#in~n;
    havoc sort_~pass~0;
    havoc sort_~i~0;
    sort_~pass~0 := 1;
    goto loc1;
  loc1:
    assume sort_~pass~0 < sort_~n;
    sort_~i~0 := 0;
    goto loc2;
  loc2:
    goto loc3;
  loc3:
    goto loc3_0, loc3_1;
  loc3_0:
    assume !(sort_~pass~0 + sort_~i~0 < sort_~n);
    sort_#t~post2 := sort_~pass~0;
    sort_~pass~0 := sort_#t~post2 + 1;
    havoc sort_#t~post2;
    goto loc1;
  loc3_1:
    assume sort_~pass~0 + sort_~i~0 < sort_~n;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := sort_~x.base, sort_~x.offset + 4 * sort_~i~0, 4;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume #valid[read~int_#ptr.base] == 1;
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    sort_#t~mem4 := read~int_#value;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := sort_~x.base, sort_~x.offset + 4 * sort_~i~0 + 4, 4;
    assume #valid[read~int_#ptr.base] == 1;
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume !(0 <= read~int_#ptr.offset) || !(read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base]);
    goto loc5;
  loc4_1:
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    sort_#t~mem5 := read~int_#value;
    assume !(sort_#t~mem5 < sort_#t~mem4);
    havoc sort_#t~mem4;
    havoc sort_#t~mem5;
    sort_#t~post3 := sort_~i~0;
    sort_~i~0 := sort_#t~post3 + 1;
    havoc sort_#t~post3;
    goto loc2;
  loc5:
    assert false;
}

