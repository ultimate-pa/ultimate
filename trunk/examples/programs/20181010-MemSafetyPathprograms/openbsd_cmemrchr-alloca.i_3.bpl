var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var read~int_#value : int;
    var main_~nondetArea~0.offset : int;
    var cmemrchr_~s.base : int;
    var main_#t~nondet5 : int;
    var main_~nondetArea~0.base : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~ret9.offset : int;
    var main_#t~nondet6 : int;
    var cmemrchr_#res.base : int;
    var main_#t~nondet7 : int;
    var cmemrchr_~cp~0.offset : int;
    var cmemrchr_#in~n : int;
    var cmemrchr_~s.offset : int;
    var cmemrchr_#in~c : int;
    var cmemrchr_#t~pre3.base : int;
    var cmemrchr_#in~s.base : int;
    var #Ultimate.alloc_#res.base : int;
    var main_#t~malloc8.base : int;
    var cmemrchr_#res.offset : int;
    var #Ultimate.alloc_#res.offset : int;
    var #Ultimate.alloc_~size : int;
    var cmemrchr_~cp~0.base : int;
    var cmemrchr_~c : int;
    var main_~n~0 : int;
    var main_~c~0 : int;
    var cmemrchr_#t~pre2 : int;
    var read~int_#sizeOfReadType : int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var cmemrchr_~n : int;
    var read~int_#ptr.base : int;
    var cmemrchr_#t~pre3.offset : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_#t~malloc8.offset : int;
    var cmemrchr_#t~mem4 : int;
    var main_#t~ret9.base : int;
    var main_~length~0 : int;
    var cmemrchr_#in~s.offset : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~malloc8.base, main_~nondetArea~0.offset, main_#t~nondet5, main_#t~malloc8.offset, main_~n~0, main_~c~0, main_~nondetArea~0.base, main_#t~ret9.offset, main_#t~nondet6, main_#t~nondet7, main_#t~ret9.base, main_~length~0;
    assume main_#t~nondet5 <= 2147483647 && 0 <= main_#t~nondet5 + 2147483648;
    main_~length~0 := main_#t~nondet5;
    havoc main_#t~nondet5;
    assume main_#t~nondet6 <= 2147483647 && 0 <= main_#t~nondet6 + 2147483648;
    main_~n~0 := main_#t~nondet6;
    havoc main_#t~nondet6;
    assume main_#t~nondet7 <= 2147483647 && 0 <= main_#t~nondet7 + 2147483648;
    main_~c~0 := main_#t~nondet7;
    havoc main_#t~nondet7;
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
    main_#t~malloc8.base, main_#t~malloc8.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~nondetArea~0.offset, main_~nondetArea~0.base := main_#t~malloc8.offset, main_#t~malloc8.base;
    cmemrchr_#in~c, cmemrchr_#in~s.base, cmemrchr_#in~n, cmemrchr_#in~s.offset := main_~c~0, main_~nondetArea~0.base, main_~n~0, main_~nondetArea~0.offset;
    havoc cmemrchr_#res.offset, cmemrchr_#res.base;
    havoc cmemrchr_~s.offset, cmemrchr_~n, cmemrchr_#t~pre3.base, cmemrchr_~s.base, cmemrchr_#t~pre3.offset, cmemrchr_~cp~0.base, cmemrchr_~c, cmemrchr_#t~mem4, cmemrchr_#t~pre2, cmemrchr_~cp~0.offset;
    cmemrchr_~s.offset, cmemrchr_~s.base := cmemrchr_#in~s.offset, cmemrchr_#in~s.base;
    cmemrchr_~c := cmemrchr_#in~c;
    cmemrchr_~n := cmemrchr_#in~n;
    havoc cmemrchr_~cp~0.base, cmemrchr_~cp~0.offset;
    assume !(0 == cmemrchr_~n % 4294967296);
    cmemrchr_~cp~0.base, cmemrchr_~cp~0.offset := cmemrchr_~s.base, (if cmemrchr_~n % 4294967296 <= 2147483647 then cmemrchr_~n % 4294967296 else cmemrchr_~n % 4294967296 + -4294967296) + cmemrchr_~s.offset;
    goto loc1;
  loc1:
    cmemrchr_#t~pre3.base, cmemrchr_#t~pre3.offset := cmemrchr_~cp~0.base, cmemrchr_~cp~0.offset + -1;
    cmemrchr_~cp~0.base, cmemrchr_~cp~0.offset := cmemrchr_~cp~0.base, cmemrchr_~cp~0.offset + -1;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := cmemrchr_#t~pre3.base, cmemrchr_#t~pre3.offset, 1;
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
    cmemrchr_#t~mem4 := read~int_#value;
    assume !(cmemrchr_~c % 256 == cmemrchr_#t~mem4 % 256);
    havoc cmemrchr_#t~mem4;
    havoc cmemrchr_#t~pre3.base, cmemrchr_#t~pre3.offset;
    cmemrchr_#t~pre2 := cmemrchr_~n + -1;
    cmemrchr_~n := cmemrchr_~n + -1;
    assume !(0 == cmemrchr_#t~pre2 % 4294967296);
    havoc cmemrchr_#t~pre2;
    goto loc1;
  loc3:
    assert false;
}

