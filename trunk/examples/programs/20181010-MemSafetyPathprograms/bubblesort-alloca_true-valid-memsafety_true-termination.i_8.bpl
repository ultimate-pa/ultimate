var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var read~int_#value : int;
    var bubbleSort_~i~0 : int;
    var main_#t~nondet8 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var bubbleSort_~numbers.base : int;
    var bubbleSort_~temp~0 : int;
    var bubbleSort_#t~mem4 : int;
    var bubbleSort_#t~mem5 : int;
    var bubbleSort_#t~post2 : int;
    var bubbleSort_#in~numbers.base : int;
    var bubbleSort_~j~0 : int;
    var main_~numbers~0.base : int;
    var bubbleSort_#t~post3 : int;
    var bubbleSort_~array_size : int;
    var main_#t~malloc9.offset : int;
    var bubbleSort_#t~mem6 : int;
    var #Ultimate.alloc_#res.base : int;
    var bubbleSort_#t~mem7 : int;
    var #Ultimate.alloc_#res.offset : int;
    var main_#t~malloc9.base : int;
    var #Ultimate.alloc_~size : int;
    var bubbleSort_#in~array_size : int;
    var bubbleSort_#in~numbers.offset : int;
    var read~int_#sizeOfReadType : int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var bubbleSort_~numbers.offset : int;
    var read~int_#ptr.base : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_~array_size~0 : int;
    var main_~numbers~0.offset : int;

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
    bubbleSort_#in~array_size, bubbleSort_#in~numbers.base, bubbleSort_#in~numbers.offset := main_~array_size~0, main_~numbers~0.base, main_~numbers~0.offset;
    havoc bubbleSort_#t~mem4, bubbleSort_#t~mem5, bubbleSort_~numbers.offset, bubbleSort_#t~post2, bubbleSort_~i~0, bubbleSort_~j~0, bubbleSort_#t~post3, bubbleSort_~array_size, bubbleSort_#t~mem6, bubbleSort_#t~mem7, bubbleSort_~numbers.base, bubbleSort_~temp~0;
    bubbleSort_~numbers.offset, bubbleSort_~numbers.base := bubbleSort_#in~numbers.offset, bubbleSort_#in~numbers.base;
    bubbleSort_~array_size := bubbleSort_#in~array_size;
    havoc bubbleSort_~i~0;
    havoc bubbleSort_~j~0;
    havoc bubbleSort_~temp~0;
    bubbleSort_~i~0 := bubbleSort_~array_size + -1;
    goto loc1;
  loc1:
    assume 0 <= bubbleSort_~i~0;
    bubbleSort_~j~0 := 1;
    goto loc2;
  loc2:
    goto loc3;
  loc3:
    goto loc3_0, loc3_1;
  loc3_0:
    assume !(bubbleSort_~j~0 <= bubbleSort_~i~0);
    bubbleSort_#t~post2 := bubbleSort_~i~0;
    bubbleSort_~i~0 := bubbleSort_#t~post2 + -1;
    havoc bubbleSort_#t~post2;
    goto loc1;
  loc3_1:
    assume bubbleSort_~j~0 <= bubbleSort_~i~0;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := bubbleSort_~numbers.base, bubbleSort_~numbers.offset + 4 * bubbleSort_~j~0 + -4, 4;
    assume 1 == #valid[read~int_#ptr.base];
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume !(read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base]) || !(0 <= read~int_#ptr.offset);
    goto loc5;
  loc4_1:
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume #valid[read~int_#ptr.base] == 1;
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    bubbleSort_#t~mem4 := read~int_#value;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := bubbleSort_~numbers.base, bubbleSort_~numbers.offset + 4 * bubbleSort_~j~0, 4;
    assume #valid[read~int_#ptr.base] == 1;
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    bubbleSort_#t~mem5 := read~int_#value;
    assume !(bubbleSort_#t~mem5 < bubbleSort_#t~mem4);
    havoc bubbleSort_#t~mem5;
    havoc bubbleSort_#t~mem4;
    bubbleSort_#t~post3 := bubbleSort_~j~0;
    bubbleSort_~j~0 := bubbleSort_#t~post3 + 1;
    havoc bubbleSort_#t~post3;
    goto loc2;
  loc5:
    assert false;
}

