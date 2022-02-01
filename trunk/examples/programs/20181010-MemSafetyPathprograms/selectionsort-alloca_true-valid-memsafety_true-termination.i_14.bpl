var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var read~int_#value : int;
    var SelectionSort_~min~0 : int;
    var main_#t~nondet8 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var SelectionSort_~temp~0 : int;
    var SelectionSort_#t~pre3 : int;
    var SelectionSort_~a.base : int;
    var SelectionSort_#t~pre2 : int;
    var SelectionSort_~array_size : int;
    var SelectionSort_#t~mem5 : int;
    var SelectionSort_#t~mem4 : int;
    var main_~numbers~0.base : int;
    var SelectionSort_#in~array_size : int;
    var SelectionSort_#t~mem7 : int;
    var SelectionSort_#t~mem6 : int;
    var main_#t~malloc9.offset : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var main_#t~malloc9.base : int;
    var #Ultimate.alloc_~size : int;
    var SelectionSort_~i~0 : int;
    var read~int_#sizeOfReadType : int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var SelectionSort_#in~a.offset : int;
    var SelectionSort_~j~0 : int;
    var read~int_#ptr.base : int;
    var SelectionSort_~a.offset : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_~array_size~0 : int;
    var main_~numbers~0.offset : int;
    var SelectionSort_#in~a.base : int;

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
    SelectionSort_#in~array_size, SelectionSort_#in~a.base, SelectionSort_#in~a.offset := main_~array_size~0, main_~numbers~0.base, main_~numbers~0.offset;
    havoc SelectionSort_~i~0, SelectionSort_~min~0, SelectionSort_~j~0, SelectionSort_~temp~0, SelectionSort_#t~pre3, SelectionSort_~a.base, SelectionSort_#t~pre2, SelectionSort_~array_size, SelectionSort_#t~mem5, SelectionSort_#t~mem4, SelectionSort_~a.offset, SelectionSort_#t~mem7, SelectionSort_#t~mem6;
    SelectionSort_~a.base, SelectionSort_~a.offset := SelectionSort_#in~a.base, SelectionSort_#in~a.offset;
    SelectionSort_~array_size := SelectionSort_#in~array_size;
    havoc SelectionSort_~i~0;
    SelectionSort_~i~0 := 0;
    assume SelectionSort_~i~0 + 1 < SelectionSort_~array_size;
    havoc SelectionSort_~j~0;
    havoc SelectionSort_~min~0;
    havoc SelectionSort_~temp~0;
    SelectionSort_~min~0 := SelectionSort_~i~0;
    SelectionSort_~j~0 := SelectionSort_~i~0 + 1;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(SelectionSort_~j~0 < SelectionSort_~array_size);
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := SelectionSort_~a.base, 4 * SelectionSort_~i~0 + SelectionSort_~a.offset, 4;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume #valid[read~int_#ptr.base] == 1;
    assume 0 <= read~int_#ptr.offset && read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base];
    havoc read~int_#value;
    assume read~int_#value == #memory_int[read~int_#ptr.base][read~int_#ptr.offset];
    SelectionSort_#t~mem6 := read~int_#value;
    SelectionSort_~temp~0 := SelectionSort_#t~mem6;
    havoc SelectionSort_#t~mem6;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := SelectionSort_~a.base, SelectionSort_~a.offset + 4 * SelectionSort_~min~0, 4;
    assume #valid[read~int_#ptr.base] == 1;
    assume !(0 <= read~int_#ptr.offset) || !(read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base]);
    goto loc3;
  loc2_1:
    assume SelectionSort_~j~0 < SelectionSort_~array_size;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := SelectionSort_~a.base, 4 * SelectionSort_~j~0 + SelectionSort_~a.offset, 4;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume #valid[read~int_#ptr.base] == 1;
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    SelectionSort_#t~mem4 := read~int_#value;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := SelectionSort_~a.base, SelectionSort_~a.offset + 4 * SelectionSort_~min~0, 4;
    assume #valid[read~int_#ptr.base] == 1;
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    SelectionSort_#t~mem5 := read~int_#value;
    goto loc4;
  loc3:
    assert false;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume SelectionSort_#t~mem4 < SelectionSort_#t~mem5;
    havoc SelectionSort_#t~mem5;
    havoc SelectionSort_#t~mem4;
    SelectionSort_~min~0 := SelectionSort_~j~0;
    goto loc5;
  loc4_1:
    assume !(SelectionSort_#t~mem4 < SelectionSort_#t~mem5);
    havoc SelectionSort_#t~mem5;
    havoc SelectionSort_#t~mem4;
    goto loc5;
  loc5:
    SelectionSort_#t~pre3 := SelectionSort_~j~0 + 1;
    SelectionSort_~j~0 := SelectionSort_~j~0 + 1;
    havoc SelectionSort_#t~pre3;
    goto loc1;
}

