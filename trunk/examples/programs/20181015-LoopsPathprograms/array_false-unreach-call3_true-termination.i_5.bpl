var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var main_#t~nondet1 : int;
    var main_~#A~0.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var read~int_#value : int;
    var #Ultimate.alloc_~size : int;
    var __VERIFIER_assert_~cond : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~post2 : int;
    var main_~i~0 : int;
    var write~int_old_#memory_int : [int][int]int;
    var main_#t~post0 : int;
    var read~int_#sizeOfReadType : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var write~int_#ptr.offset : int;
    var write~int_#sizeOfWrittenType : int;
    var write~int_#ptr.base : int;
    var read~int_#ptr.base : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var write~int_#value : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~#A~0.offset : int;
    var main_#t~mem3 : int;
    var #Ultimate.alloc_#res.base : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    havoc main_#res;
    havoc main_#t~nondet1, main_~#A~0.base, main_#t~post2, main_~i~0, main_#t~post0, main_~#A~0.offset, main_#t~mem3;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4096;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_~#A~0.base, main_~#A~0.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    havoc main_~i~0;
    main_~i~0 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~i~0 < 1024);
    main_~i~0 := 0;
    goto loc3;
  loc2_1:
    assume main_~i~0 < 1024;
    assume 0 <= main_#t~nondet1 + 2147483648 && main_#t~nondet1 <= 2147483647;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, main_~#A~0.base, main_#t~nondet1, main_~#A~0.offset + 4 * main_~i~0;
    havoc #memory_int;
    assume write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]] == #memory_int;
    havoc main_#t~nondet1;
    main_#t~post0 := main_~i~0;
    main_~i~0 := main_#t~post0 + 1;
    havoc main_#t~post0;
    goto loc1;
  loc3:
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := main_~#A~0.base, main_~#A~0.offset + 4 * main_~i~0, 4;
    havoc read~int_#value;
    assume read~int_#value == #memory_int[read~int_#ptr.base][read~int_#ptr.offset];
    main_#t~mem3 := read~int_#value;
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume main_#t~mem3 == 0 || !(main_~i~0 < 1024);
    havoc main_#t~mem3;
    __VERIFIER_assert_#in~cond := (if main_~i~0 <= 512 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume 0 == __VERIFIER_assert_~cond;
    goto loc5;
  loc4_1:
    assume main_~i~0 < 1024 && !(main_#t~mem3 == 0);
    havoc main_#t~mem3;
    main_#t~post2 := main_~i~0;
    main_~i~0 := main_#t~post2 + 1;
    havoc main_#t~post2;
    goto loc3;
  loc5:
    assert false;
}

