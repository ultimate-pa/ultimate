var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var read~int_#value : int;
    var main_#t~nondet8 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~nondet9 : int;
    var main_#t~nondet6 : int;
    var cstrreplace_#res : int;
    var cstrreplace_~p~0.offset : int;
    var cstrreplace_~numReplaced~0 : int;
    var write~int_#ptr.offset : int;
    var main_#t~malloc7.offset : int;
    var write~int_#ptr.base : int;
    var cstrreplace_~new : int;
    var main_~nondetString1~0.base : int;
    var cstrreplace_#in~s.base : int;
    var cstrreplace_#in~s.offset : int;
    var cstrreplace_#t~post5.offset : int;
    var cstrreplace_~s.offset : int;
    var cstrreplace_#in~new : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var cstrreplace_~old : int;
    var main_#t~malloc7.base : int;
    var #Ultimate.alloc_~size : int;
    var main_~length1~0 : int;
    var write~int_old_#memory_int : [int][int]int;
    var cstrreplace_#in~old : int;
    var read~int_#sizeOfReadType : int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var cstrreplace_#t~mem2 : int;
    var cstrreplace_#t~mem3 : int;
    var write~int_#sizeOfWrittenType : int;
    var cstrreplace_~s.base : int;
    var read~int_#ptr.base : int;
    var cstrreplace_#t~post5.base : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_#t~ret10 : int;
    var main_~nondetString1~0.offset : int;
    var write~int_#value : int;
    var cstrreplace_#t~post4 : int;
    var cstrreplace_~p~0.base : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~malloc7.base, main_#t~ret10, main_~nondetString1~0.base, main_#t~nondet8, main_#t~nondet9, main_~length1~0, main_~nondetString1~0.offset, main_#t~nondet6, main_#t~malloc7.offset;
    assume main_#t~nondet6 <= 2147483647 && 0 <= main_#t~nondet6 + 2147483648;
    main_~length1~0 := main_#t~nondet6;
    havoc main_#t~nondet6;
    assume !(main_~length1~0 < 1);
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := main_~length1~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc7.base, main_#t~malloc7.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~nondetString1~0.base, main_~nondetString1~0.offset := main_#t~malloc7.base, main_#t~malloc7.offset;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 1, main_~nondetString1~0.base, 0, main_~nondetString1~0.offset + main_~length1~0 + -1;
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    havoc #memory_int;
    assume #memory_int == write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]];
    assume 0 <= main_#t~nondet8 + 2147483648 && main_#t~nondet8 <= 2147483647;
    assume 0 <= main_#t~nondet9 + 2147483648 && main_#t~nondet9 <= 2147483647;
    cstrreplace_#in~s.base, cstrreplace_#in~s.offset, cstrreplace_#in~old, cstrreplace_#in~new := main_~nondetString1~0.base, main_~nondetString1~0.offset, (if main_#t~nondet8 % 256 <= 127 then main_#t~nondet8 % 256 else main_#t~nondet8 % 256 + -256), (if main_#t~nondet9 % 256 <= 127 then main_#t~nondet9 % 256 else main_#t~nondet9 % 256 + -256);
    havoc cstrreplace_#res;
    havoc cstrreplace_~old, cstrreplace_~s.base, cstrreplace_#t~post5.base, cstrreplace_~new, cstrreplace_#t~post5.offset, cstrreplace_#t~post4, cstrreplace_~s.offset, cstrreplace_~p~0.base, cstrreplace_~p~0.offset, cstrreplace_~numReplaced~0, cstrreplace_#t~mem2, cstrreplace_#t~mem3;
    cstrreplace_~s.base, cstrreplace_~s.offset := cstrreplace_#in~s.base, cstrreplace_#in~s.offset;
    cstrreplace_~old := cstrreplace_#in~old;
    cstrreplace_~new := cstrreplace_#in~new;
    cstrreplace_~p~0.base, cstrreplace_~p~0.offset := cstrreplace_~s.base, cstrreplace_~s.offset;
    cstrreplace_~numReplaced~0 := 0;
    goto loc1;
  loc1:
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := cstrreplace_~p~0.base, cstrreplace_~p~0.offset, 1;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(#valid[read~int_#ptr.base] == 1);
    goto loc3;
  loc2_1:
    assume 1 == #valid[read~int_#ptr.base];
    assume 0 <= read~int_#ptr.offset && read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base];
    assume #valid[read~int_#ptr.base] == 1;
    assume 0 <= read~int_#ptr.offset && read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base];
    havoc read~int_#value;
    assume read~int_#value == #memory_int[read~int_#ptr.base][read~int_#ptr.offset];
    cstrreplace_#t~mem2 := read~int_#value;
    assume !(cstrreplace_#t~mem2 == 0);
    havoc cstrreplace_#t~mem2;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := cstrreplace_~p~0.base, cstrreplace_~p~0.offset, 1;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    cstrreplace_#t~mem3 := read~int_#value;
    assume !(cstrreplace_#t~mem3 == cstrreplace_~old);
    havoc cstrreplace_#t~mem3;
    cstrreplace_#t~post5.base, cstrreplace_#t~post5.offset := cstrreplace_~p~0.base, cstrreplace_~p~0.offset;
    cstrreplace_~p~0.base, cstrreplace_~p~0.offset := cstrreplace_#t~post5.base, cstrreplace_#t~post5.offset + 1;
    havoc cstrreplace_#t~post5.base, cstrreplace_#t~post5.offset;
    goto loc1;
  loc3:
    assert false;
}

