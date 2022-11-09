var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var test_fun_#in~a.base : int;
    var read~int_#value : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~nondet7 : int;
    var write~int_#ptr.offset : int;
    var test_fun_#t~mem4 : int;
    var test_fun_~a.offset : int;
    var test_fun_~a.base : int;
    var test_fun_#t~post5 : int;
    var test_fun_#in~a.offset : int;
    var test_fun_#t~post6 : int;
    var test_fun_#t~mem3 : int;
    var write~int_#ptr.base : int;
    var main_~numbers~0.base : int;
    var test_fun_#res : int;
    var test_fun_#t~post2 : int;
    var #Ultimate.alloc_#res.base : int;
    var main_#t~malloc8.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var #Ultimate.alloc_~size : int;
    var test_fun_~res~0 : int;
    var write~int_old_#memory_int : [int][int]int;
    var read~int_#sizeOfReadType : int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var test_fun_#in~N : int;
    var write~int_#sizeOfWrittenType : int;
    var read~int_#ptr.base : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_#t~malloc8.offset : int;
    var main_~array_size~0 : int;
    var main_#t~ret9 : int;
    var main_~numbers~0.offset : int;
    var write~int_#value : int;
    var test_fun_~N : int;
    var test_fun_~i~0 : int;

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
    test_fun_#in~N, test_fun_#in~a.base, test_fun_#in~a.offset := main_~array_size~0, main_~numbers~0.base, main_~numbers~0.offset;
    havoc test_fun_#res;
    havoc test_fun_#t~mem4, test_fun_~a.offset, test_fun_~a.base, test_fun_#t~post5, test_fun_#t~post6, test_fun_#t~mem3, test_fun_~res~0, test_fun_#t~post2, test_fun_~N, test_fun_~i~0;
    test_fun_~a.offset, test_fun_~a.base := test_fun_#in~a.offset, test_fun_#in~a.base;
    test_fun_~N := test_fun_#in~N;
    havoc test_fun_~i~0;
    test_fun_~res~0 := 0;
    test_fun_~i~0 := 0;
    goto loc1;
  loc1:
    assume test_fun_~i~0 < test_fun_~N;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := test_fun_~a.base, 4 * test_fun_~i~0 + test_fun_~a.offset, 4;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume #valid[read~int_#ptr.base] == 1;
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    test_fun_#t~mem3 := read~int_#value;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(0 < test_fun_#t~mem3);
    havoc test_fun_#t~mem3;
    test_fun_#t~post2 := test_fun_~i~0;
    test_fun_~i~0 := test_fun_#t~post2 + 1;
    havoc test_fun_#t~post2;
    goto loc1;
  loc2_1:
    assume 0 < test_fun_#t~mem3;
    havoc test_fun_#t~mem3;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := test_fun_~a.base, 4 * test_fun_~i~0 + test_fun_~a.offset, 4;
    assume #valid[read~int_#ptr.base] == 1;
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    test_fun_#t~mem4 := read~int_#value;
    test_fun_#t~post5 := test_fun_#t~mem4;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, test_fun_~a.base, test_fun_#t~post5 + -1, 4 * test_fun_~i~0 + test_fun_~a.offset;
    assume 1 == #valid[write~int_#ptr.base];
    assume !(write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base]) || !(0 <= write~int_#ptr.offset);
    goto loc3;
  loc3:
    assert false;
}

