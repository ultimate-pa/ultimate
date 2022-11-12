var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var read~int_#value : int;
    var diff_~Alen : int;
    var main_#t~malloc11.offset : int;
    var diff_#in~Blen : int;
    var main_#t~nondet8 : int;
    var main_#t~malloc12.base : int;
    var main_#t~malloc11.base : int;
    var diff_#in~A.offset : int;
    var main_~D~0.offset : int;
    var diff_#in~D.offset : int;
    var diff_#in~Alen : int;
    var write~int_#ptr.base : int;
    var main_~A~0.offset : int;
    var #Ultimate.alloc_#res.base : int;
    var diff_~Blen : int;
    var #Ultimate.alloc_#res.offset : int;
    var main_~A~0.base : int;
    var diff_#t~mem2 : int;
    var diff_#t~post4 : int;
    var diff_#in~B.offset : int;
    var diff_~i~0 : int;
    var diff_#t~post6 : int;
    var write~int_old_#memory_int : [int][int]int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var main_#t~malloc12.offset : int;
    var write~int_#sizeOfWrittenType : int;
    var read~int_#ptr.base : int;
    var diff_~j~0 : int;
    var diff_~k~0 : int;
    var write~int_#value : int;
    var diff_~A.offset : int;
    var diff_#in~A.base : int;
    var diff_#in~B.base : int;
    var diff_~B.offset : int;
    var diff_~D.base : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~nondet9 : int;
    var main_~B~0.offset : int;
    var main_~B~0.base : int;
    var write~int_#ptr.offset : int;
    var diff_~A.base : int;
    var diff_~B.base : int;
    var diff_#t~mem3 : int;
    var diff_#t~mem5 : int;
    var main_#t~malloc10.offset : int;
    var main_~Alen~0 : int;
    var main_~Blen~0 : int;
    var #Ultimate.alloc_~size : int;
    var diff_~found~0 : int;
    var diff_~l1~0 : int;
    var diff_#t~post7 : int;
    var read~int_#sizeOfReadType : int;
    var main_#t~malloc10.base : int;
    var diff_~D.offset : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var diff_~l2~0 : int;
    var diff_#in~D.base : int;
    var main_~D~0.base : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_~A~0.base, main_#t~malloc11.offset, main_#t~nondet8, main_#t~nondet9, main_#t~malloc12.base, main_~B~0.offset, main_#t~malloc11.base, main_~B~0.base, main_#t~malloc12.offset, main_~D~0.offset, main_#t~malloc10.base, main_~D~0.base, main_~A~0.offset, main_#t~malloc10.offset, main_~Alen~0, main_~Blen~0;
    assume 0 <= main_#t~nondet8 + 2147483648 && main_#t~nondet8 <= 2147483647;
    main_~Alen~0 := main_#t~nondet8;
    havoc main_#t~nondet8;
    assume 0 <= main_#t~nondet9 + 2147483648 && main_#t~nondet9 <= 2147483647;
    main_~Blen~0 := main_#t~nondet9;
    havoc main_#t~nondet9;
    assume !(536870911 <= main_~Alen~0) && !(main_~Alen~0 < 1);
    assume !(main_~Blen~0 < 1) && !(536870911 <= main_~Blen~0);
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4 * main_~Alen~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc10.base, main_#t~malloc10.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~A~0.base, main_~A~0.offset := main_#t~malloc10.base, main_#t~malloc10.offset;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4 * main_~Blen~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #length == #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size];
    main_#t~malloc11.offset, main_#t~malloc11.base := #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    main_~B~0.offset, main_~B~0.base := main_#t~malloc11.offset, main_#t~malloc11.base;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4 * main_~Alen~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc12.offset, main_#t~malloc12.base := #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    main_~D~0.offset, main_~D~0.base := main_#t~malloc12.offset, main_#t~malloc12.base;
    diff_#in~A.base, diff_#in~B.base, diff_#in~D.offset, diff_#in~Alen, diff_#in~B.offset, diff_#in~Blen, diff_#in~D.base, diff_#in~A.offset := main_~A~0.base, main_~B~0.base, main_~D~0.offset, main_~Alen~0, main_~B~0.offset, main_~Blen~0, main_~D~0.base, main_~A~0.offset;
    havoc diff_#t~mem2, diff_~Alen, diff_~B.offset, diff_#t~post4, diff_~found~0, diff_~D.base, diff_~i~0, diff_~l1~0, diff_#t~post6, diff_#t~post7, diff_~D.offset, diff_~j~0, diff_~A.base, diff_~l2~0, diff_~k~0, diff_~B.base, diff_~A.offset, diff_#t~mem3, diff_#t~mem5, diff_~Blen;
    diff_~A.base, diff_~A.offset := diff_#in~A.base, diff_#in~A.offset;
    diff_~Alen := diff_#in~Alen;
    diff_~B.offset, diff_~B.base := diff_#in~B.offset, diff_#in~B.base;
    diff_~Blen := diff_#in~Blen;
    diff_~D.offset, diff_~D.base := diff_#in~D.offset, diff_#in~D.base;
    diff_~k~0 := 0;
    diff_~i~0 := 0;
    diff_~l1~0 := diff_~Alen;
    diff_~l2~0 := diff_~Blen;
    havoc diff_~found~0;
    goto loc1;
  loc1:
    assume diff_~i~0 < diff_~l1~0;
    diff_~j~0 := 0;
    diff_~found~0 := 0;
    goto loc2;
  loc2:
    goto loc3;
  loc3:
    goto loc3_0, loc3_1;
  loc3_0:
    assume !(diff_~j~0 < diff_~l2~0) || !(0 == diff_~found~0);
    goto loc4;
  loc3_1:
    assume 0 == diff_~found~0 && diff_~j~0 < diff_~l2~0;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := diff_~A.base, 4 * diff_~i~0 + diff_~A.offset, 4;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume 1 == #valid[read~int_#ptr.base];
    assume read~int_#sizeOfReadType + read~int_#ptr.offset <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    diff_#t~mem2 := read~int_#value;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := diff_~B.base, 4 * diff_~j~0 + diff_~B.offset, 4;
    assume #valid[read~int_#ptr.base] == 1;
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume #valid[read~int_#ptr.base] == 1;
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    havoc read~int_#value;
    assume #memory_int[read~int_#ptr.base][read~int_#ptr.offset] == read~int_#value;
    diff_#t~mem3 := read~int_#value;
    goto loc5;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume 0 == diff_~found~0;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := diff_~A.base, 4 * diff_~i~0 + diff_~A.offset, 4;
    assume #valid[read~int_#ptr.base] == 1;
    assume read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base] && 0 <= read~int_#ptr.offset;
    assume #valid[read~int_#ptr.base] == 1;
    assume 0 <= read~int_#ptr.offset && read~int_#ptr.offset + read~int_#sizeOfReadType <= #length[read~int_#ptr.base];
    havoc read~int_#value;
    assume read~int_#value == #memory_int[read~int_#ptr.base][read~int_#ptr.offset];
    diff_#t~mem5 := read~int_#value;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, diff_~D.base, diff_#t~mem5, 4 * diff_~k~0 + diff_~D.offset;
    assume 1 == #valid[write~int_#ptr.base];
    goto loc6;
  loc4_1:
    assume !(0 == diff_~found~0);
    goto loc7;
  loc5:
    goto loc5_0, loc5_1;
  loc5_0:
    assume diff_#t~mem3 == diff_#t~mem2;
    havoc diff_#t~mem2;
    havoc diff_#t~mem3;
    diff_~found~0 := 1;
    goto loc2;
  loc5_1:
    assume !(diff_#t~mem3 == diff_#t~mem2);
    havoc diff_#t~mem2;
    havoc diff_#t~mem3;
    diff_#t~post4 := diff_~j~0;
    diff_~j~0 := diff_#t~post4 + 1;
    havoc diff_#t~post4;
    goto loc2;
  loc6:
    goto loc6_0, loc6_1;
  loc6_0:
    assume !(0 <= write~int_#ptr.offset) || !(write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base]);
    goto loc8;
  loc6_1:
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    assume 1 == #valid[write~int_#ptr.base];
    assume write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base] && 0 <= write~int_#ptr.offset;
    havoc #memory_int;
    assume #memory_int == write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]];
    havoc diff_#t~mem5;
    diff_#t~post6 := diff_~k~0;
    diff_~k~0 := diff_#t~post6 + 1;
    havoc diff_#t~post6;
    goto loc7;
  loc7:
    diff_#t~post7 := diff_~i~0;
    diff_~i~0 := diff_#t~post7 + 1;
    havoc diff_#t~post7;
    goto loc1;
  loc8:
    assert false;
}

