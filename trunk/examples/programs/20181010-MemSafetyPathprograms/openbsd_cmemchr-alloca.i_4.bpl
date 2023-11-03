var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var cmemchr_~s.base : int;
    var read~int_#value : int;
    var main_~nondetArea~0.offset : int;
    var main_#t~nondet5 : int;
    var main_~nondetArea~0.base : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var cmemchr_~p~0.offset : int;
    var main_#t~ret9.offset : int;
    var main_#t~nondet6 : int;
    var main_#t~nondet7 : int;
    var cmemchr_~n : int;
    var cmemchr_#in~s.offset : int;
    var cmemchr_#res.base : int;
    var cmemchr_~s.offset : int;
    var cmemchr_#in~n : int;
    var cmemchr_#t~mem4 : int;
    var cmemchr_#res.offset : int;
    var #Ultimate.alloc_#res.base : int;
    var main_#t~malloc8.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var #Ultimate.alloc_~size : int;
    var cmemchr_#in~c : int;
    var cmemchr_#in~s.base : int;
    var cmemchr_#t~pre2 : int;
    var main_~n~0 : int;
    var main_~c~0 : int;
    var read~int_#sizeOfReadType : int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var cmemchr_#t~post3.base : int;
    var cmemchr_~p~0.base : int;
    var cmemchr_~c : int;
    var cmemchr_#t~post3.offset : int;
    var read~int_#ptr.base : int;
    var read~int_#ptr.offset : int;
    var main_#res : int;
    var main_#t~malloc8.offset : int;
    var main_#t~ret9.base : int;
    var main_~length~0 : int;

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
    cmemchr_#in~c, cmemchr_#in~s.base, cmemchr_#in~n, cmemchr_#in~s.offset := main_~c~0, main_~nondetArea~0.base, main_~n~0, main_~nondetArea~0.offset;
    havoc cmemchr_#res.base, cmemchr_#res.offset;
    havoc cmemchr_~p~0.base, cmemchr_~s.base, cmemchr_~c, cmemchr_#t~post3.offset, cmemchr_~s.offset, cmemchr_#t~pre2, cmemchr_#t~mem4, cmemchr_~p~0.offset, cmemchr_~n, cmemchr_#t~post3.base;
    cmemchr_~s.base, cmemchr_~s.offset := cmemchr_#in~s.base, cmemchr_#in~s.offset;
    cmemchr_~c := cmemchr_#in~c;
    cmemchr_~n := cmemchr_#in~n;
    assume !(0 == cmemchr_~n % 4294967296);
    cmemchr_~p~0.base, cmemchr_~p~0.offset := cmemchr_~s.base, cmemchr_~s.offset;
    goto loc1;
  loc1:
    cmemchr_#t~post3.offset, cmemchr_#t~post3.base := cmemchr_~p~0.offset, cmemchr_~p~0.base;
    cmemchr_~p~0.base, cmemchr_~p~0.offset := cmemchr_#t~post3.base, cmemchr_#t~post3.offset + 1;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := cmemchr_#t~post3.base, cmemchr_#t~post3.offset, 1;
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
    cmemchr_#t~mem4 := read~int_#value;
    assume !(cmemchr_~c % 256 == cmemchr_#t~mem4 % 256);
    havoc cmemchr_#t~post3.offset, cmemchr_#t~post3.base;
    havoc cmemchr_#t~mem4;
    cmemchr_#t~pre2 := cmemchr_~n + -1;
    cmemchr_~n := cmemchr_~n + -1;
    assume !(cmemchr_#t~pre2 % 4294967296 == 0);
    havoc cmemchr_#t~pre2;
    goto loc1;
  loc3:
    assert false;
}

