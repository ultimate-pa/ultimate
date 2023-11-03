var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var cmemset_~d~0.offset : int;
    var main_~nondetArea~0.offset : int;
    var cmemset_#res.base : int;
    var cmemset_~dst.offset : int;
    var main_#t~nondet4 : int;
    var main_#t~nondet5 : int;
    var main_~nondetArea~0.base : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var cmemset_#t~post3.offset : int;
    var main_#t~nondet6 : int;
    var write~int_#ptr.offset : int;
    var main_#t~malloc7.offset : int;
    var cmemset_#in~dst.base : int;
    var write~int_#ptr.base : int;
    var cmemset_#t~post3.base : int;
    var cmemset_#in~dst.offset : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var main_#t~malloc7.base : int;
    var main_#t~ret8.base : int;
    var #Ultimate.alloc_~size : int;
    var main_~n~0 : int;
    var main_~c~0 : int;
    var write~int_old_#memory_int : [int][int]int;
    var cmemset_#in~n : int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var cmemset_~d~0.base : int;
    var cmemset_~dst.base : int;
    var cmemset_~c : int;
    var write~int_#sizeOfWrittenType : int;
    var main_#res : int;
    var cmemset_#res.offset : int;
    var write~int_#value : int;
    var cmemset_#t~pre2 : int;
    var cmemset_~n : int;
    var main_#t~ret8.offset : int;
    var main_~length~0 : int;
    var cmemset_#in~c : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~malloc7.base, main_#t~ret8.base, main_~nondetArea~0.offset, main_#t~nondet4, main_#t~nondet5, main_~n~0, main_~c~0, main_~nondetArea~0.base, main_#t~nondet6, main_#t~ret8.offset, main_~length~0, main_#t~malloc7.offset;
    assume main_#t~nondet4 <= 2147483647 && 0 <= main_#t~nondet4 + 2147483648;
    main_~length~0 := main_#t~nondet4;
    havoc main_#t~nondet4;
    assume main_#t~nondet5 <= 2147483647 && 0 <= main_#t~nondet5 + 2147483648;
    main_~n~0 := main_#t~nondet5;
    havoc main_#t~nondet5;
    assume main_#t~nondet6 <= 2147483647 && 0 <= main_#t~nondet6 + 2147483648;
    main_~c~0 := main_#t~nondet6;
    havoc main_#t~nondet6;
    assume !(main_~length~0 < 1);
    assume !(main_~n~0 < 1);
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := main_~n~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc7.base, main_#t~malloc7.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~nondetArea~0.offset, main_~nondetArea~0.base := main_#t~malloc7.offset, main_#t~malloc7.base;
    cmemset_#in~dst.base, cmemset_#in~dst.offset, cmemset_#in~n, cmemset_#in~c := main_~nondetArea~0.base, main_~nondetArea~0.offset, main_~n~0, main_~c~0;
    havoc cmemset_#res.base, cmemset_#res.offset;
    havoc cmemset_~dst.base, cmemset_~d~0.offset, cmemset_~c, cmemset_~dst.offset, cmemset_#t~post3.base, cmemset_#t~post3.offset, cmemset_#t~pre2, cmemset_~n, cmemset_~d~0.base;
    cmemset_~dst.base, cmemset_~dst.offset := cmemset_#in~dst.base, cmemset_#in~dst.offset;
    cmemset_~c := cmemset_#in~c;
    cmemset_~n := cmemset_#in~n;
    assume !(0 == cmemset_~n % 4294967296);
    cmemset_~d~0.offset, cmemset_~d~0.base := cmemset_~dst.offset, cmemset_~dst.base;
    goto loc1;
  loc1:
    cmemset_#t~post3.base, cmemset_#t~post3.offset := cmemset_~d~0.base, cmemset_~d~0.offset;
    cmemset_~d~0.offset, cmemset_~d~0.base := cmemset_#t~post3.offset + 1, cmemset_#t~post3.base;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 1, cmemset_#t~post3.base, cmemset_~c, cmemset_#t~post3.offset;
    assume #valid[write~int_#ptr.base] == 1;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base]) || !(0 <= write~int_#ptr.offset);
    goto loc3;
  loc2_1:
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    assume #valid[write~int_#ptr.base] == 1;
    assume 0 <= write~int_#ptr.offset && write~int_#sizeOfWrittenType + write~int_#ptr.offset <= #length[write~int_#ptr.base];
    havoc #memory_int;
    assume #memory_int == write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]];
    havoc cmemset_#t~post3.base, cmemset_#t~post3.offset;
    cmemset_#t~pre2 := cmemset_~n + -1;
    cmemset_~n := cmemset_~n + -1;
    assume !(0 == cmemset_#t~pre2 % 4294967296);
    havoc cmemset_#t~pre2;
    goto loc1;
  loc3:
    assert false;
}

