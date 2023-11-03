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
    var main_#t~nondet11 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~malloc12.base : int;
    var test_fun_#t~mem8 : int;
    var test_fun_#t~mem7 : int;
    var test_fun_#t~mem4 : int;
    var test_fun_~a.offset : int;
    var test_fun_~a.base : int;
    var test_fun_#t~post5 : int;
    var test_fun_#in~a.offset : int;
    var test_fun_#t~post6 : int;
    var test_fun_#t~mem3 : int;
    var main_~numbers~0.base : int;
    var test_fun_#t~post10 : int;
    var test_fun_#t~post2 : int;
    var test_fun_#t~post9 : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var #Ultimate.alloc_~size : int;
    var read~int_#sizeOfReadType : int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var main_#t~malloc12.offset : int;
    var test_fun_#in~N : int;
    var test_fun_~neg~0 : int;
    var read~int_#ptr.base : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_~array_size~0 : int;
    var main_~numbers~0.offset : int;
    var test_fun_~N : int;
    var test_fun_~i~0 : int;
    var test_fun_~pos~0 : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~malloc12.offset, main_#t~nondet11, main_~array_size~0, main_~numbers~0.base, main_~numbers~0.offset, main_#t~malloc12.base;
    assume 0 <= main_#t~nondet11 + 2147483648 && main_#t~nondet11 <= 2147483647;
    main_~array_size~0 := main_#t~nondet11;
    havoc main_#t~nondet11;
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
    main_#t~malloc12.offset, main_#t~malloc12.base := #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    main_~numbers~0.base, main_~numbers~0.offset := main_#t~malloc12.base, main_#t~malloc12.offset;
    test_fun_#in~N, test_fun_#in~a.base, test_fun_#in~a.offset := main_~array_size~0, main_~numbers~0.base, main_~numbers~0.offset;
    havoc test_fun_#t~mem8, test_fun_#t~mem7, test_fun_#t~mem4, test_fun_~a.offset, test_fun_~a.base, test_fun_#t~post5, test_fun_#t~post6, test_fun_#t~mem3, test_fun_~neg~0, test_fun_#t~post10, test_fun_#t~post2, test_fun_~N, test_fun_~i~0, test_fun_#t~post9, test_fun_~pos~0;
    test_fun_~a.offset, test_fun_~a.base := test_fun_#in~a.offset, test_fun_#in~a.base;
    test_fun_~N := test_fun_#in~N;
    havoc test_fun_~i~0;
    test_fun_~pos~0 := 0;
    test_fun_~neg~0 := 0;
    test_fun_~i~0 := 0;
    goto loc1;
  loc1:
    assume test_fun_~i~0 < test_fun_~N;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := test_fun_~a.base, 4 * test_fun_~i~0 + test_fun_~a.offset, 4;
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
    test_fun_#t~mem3 := read~int_#value;
    assume !(test_fun_#t~mem3 < 0);
    havoc test_fun_#t~mem3;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := test_fun_~a.base, 4 * test_fun_~i~0 + test_fun_~a.offset, 4;
    assume #valid[read~int_#ptr.base] == 1;
    assume 0 <= read~int_#ptr.offset && read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base];
    assume 1 == #valid[read~int_#ptr.base];
    assume 0 <= read~int_#ptr.offset && read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base];
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    test_fun_#t~mem7 := read~int_#value;
    assume !(0 < test_fun_#t~mem7);
    havoc test_fun_#t~mem7;
    test_fun_#t~post2 := test_fun_~i~0;
    test_fun_~i~0 := test_fun_#t~post2 + 1;
    havoc test_fun_#t~post2;
    goto loc1;
  loc3:
    assert false;
}

