var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var read~int_#value : int;
    var sumOfThirdBytes_~#numbers.offset : int;
    var sumOfThirdBytes_~array_size : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var sumOfThirdBytes_#in~array_size : int;
    var sumOfThirdBytes_~i~0 : int;
    var main_#t~nondet7 : int;
    var sumOfThirdBytes_~p~0.base : int;
    var write~int_#ptr.offset : int;
    var sumOfThirdBytes_#t~mem3 : int;
    var sumOfThirdBytes_#t~mem5 : int;
    var sumOfThirdBytes_~p~0.offset : int;
    var write~int_#ptr.base : int;
    var sumOfThirdBytes_~#numbers.base : int;
    var main_~numbers~0.base : int;
    var sumOfThirdBytes_#in~numbers.offset : int;
    var #Ultimate.alloc_#res.base : int;
    var main_#t~malloc8.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var sumOfThirdBytes_#t~post6 : int;
    var #Ultimate.alloc_~size : int;
    var write~int_old_#memory_int : [int][int]int;
    var read~int_#sizeOfReadType : int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var write~int_#sizeOfWrittenType : int;
    var read~int_#ptr.base : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_#t~malloc8.offset : int;
    var main_~array_size~0 : int;
    var main_#t~ret9 : int;
    var main_~numbers~0.offset : int;
    var write~int_#value : int;
    var sumOfThirdBytes_#in~numbers.base : int;
    var sumOfThirdBytes_#res : int;
    var sumOfThirdBytes_#t~post2 : int;
    var sumOfThirdBytes_#t~post4 : int;
    var sumOfThirdBytes_~sum~0 : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~malloc8.base, main_#t~malloc8.offset, main_~array_size~0, main_~numbers~0.base, main_#t~ret9, main_~numbers~0.offset, main_#t~nondet7;
    assume main_#t~nondet7 <= 2147483647 && 0 <= main_#t~nondet7 + 2147483648;
    main_~array_size~0 := main_#t~nondet7;
    havoc main_#t~nondet7;
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
    main_#t~malloc8.base, main_#t~malloc8.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~numbers~0.base, main_~numbers~0.offset := main_#t~malloc8.base, main_#t~malloc8.offset;
    sumOfThirdBytes_#in~array_size, sumOfThirdBytes_#in~numbers.base, sumOfThirdBytes_#in~numbers.offset := main_~array_size~0, main_~numbers~0.base, main_~numbers~0.offset;
    havoc sumOfThirdBytes_#res;
    havoc sumOfThirdBytes_#t~mem3, sumOfThirdBytes_#t~post6, sumOfThirdBytes_#t~mem5, sumOfThirdBytes_~p~0.offset, sumOfThirdBytes_~#numbers.base, sumOfThirdBytes_~#numbers.offset, sumOfThirdBytes_~array_size, sumOfThirdBytes_~i~0, sumOfThirdBytes_#t~post2, sumOfThirdBytes_~p~0.base, sumOfThirdBytes_#t~post4, sumOfThirdBytes_~sum~0;
    sumOfThirdBytes_~#numbers.base, sumOfThirdBytes_~#numbers.offset := sumOfThirdBytes_#in~numbers.base, sumOfThirdBytes_#in~numbers.offset;
    sumOfThirdBytes_~array_size := sumOfThirdBytes_#in~array_size;
    havoc sumOfThirdBytes_~i~0;
    havoc sumOfThirdBytes_~sum~0;
    havoc sumOfThirdBytes_~p~0.offset, sumOfThirdBytes_~p~0.base;
    sumOfThirdBytes_~sum~0 := 0;
    sumOfThirdBytes_~i~0 := 0;
    goto loc1;
  loc1:
    assume sumOfThirdBytes_~i~0 < sumOfThirdBytes_~array_size;
    sumOfThirdBytes_~p~0.offset, sumOfThirdBytes_~p~0.base := sumOfThirdBytes_~#numbers.offset + 4 * sumOfThirdBytes_~i~0, sumOfThirdBytes_~#numbers.base;
    sumOfThirdBytes_~p~0.offset, sumOfThirdBytes_~p~0.base := sumOfThirdBytes_~p~0.offset + 2, sumOfThirdBytes_~p~0.base;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := sumOfThirdBytes_~p~0.base, sumOfThirdBytes_~p~0.offset, 1;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume #valid[read~int_#ptr.base] == 1;
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    sumOfThirdBytes_#t~mem3 := read~int_#value;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(0 < sumOfThirdBytes_#t~mem3);
    havoc sumOfThirdBytes_#t~mem3;
    sumOfThirdBytes_#t~post2 := sumOfThirdBytes_~i~0;
    sumOfThirdBytes_~i~0 := sumOfThirdBytes_#t~post2 + 1;
    havoc sumOfThirdBytes_#t~post2;
    goto loc1;
  loc2_1:
    assume 0 < sumOfThirdBytes_#t~mem3;
    havoc sumOfThirdBytes_#t~mem3;
    sumOfThirdBytes_#t~post4 := sumOfThirdBytes_~sum~0;
    sumOfThirdBytes_~sum~0 := sumOfThirdBytes_#t~post4 + 1;
    havoc sumOfThirdBytes_#t~post4;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := sumOfThirdBytes_~p~0.base, sumOfThirdBytes_~p~0.offset, 1;
    assume #valid[read~int_#ptr.base] == 1;
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    sumOfThirdBytes_#t~mem5 := read~int_#value;
    sumOfThirdBytes_#t~post6 := sumOfThirdBytes_#t~mem5;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 1, sumOfThirdBytes_~p~0.base, sumOfThirdBytes_#t~post6 + -1, sumOfThirdBytes_~p~0.offset;
    assume 1 == #valid[write~int_#ptr.base];
    assume !(write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base]) || !(0 <= write~int_#ptr.offset);
    goto loc3;
  loc3:
    assert false;
}

