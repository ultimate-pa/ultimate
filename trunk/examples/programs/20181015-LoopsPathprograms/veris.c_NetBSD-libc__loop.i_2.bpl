var ~tmp~0.offset : int;

var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var ~tmp~0.base : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies ~tmp~0.offset, #valid, #memory_int, #NULL.offset, ~tmp~0.base, #length, #NULL.base;
{
    var glob2_~pathlim.base : int;
    var main_~#pathbuf~0.offset : int;
    var glob2_#in~pathlim.base : int;
    var glob2_~p~0.offset : int;
    var __VERIFIER_assert_~cond : int;
    var glob2_#in~pathbuf.offset : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var write~int_#ptr.offset : int;
    var glob2_#in~pathbuf.base : int;
    var write~int_#ptr.base : int;
    var glob2_#t~post0.base : int;
    var glob2_~pathbuf.base : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var #Ultimate.alloc_~size : int;
    var glob2_#res : int;
    var glob2_~pathbuf.offset : int;
    var main_~bound~0.base : int;
    var glob2_~pathlim.offset : int;
    var glob2_~p~0.base : int;
    var main_~bound~0.offset : int;
    var write~int_old_#memory_int : [int][int]int;
    var main_~#pathbuf~0.base : int;
    var glob2_#t~post0.offset : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var main_#t~ret1 : int;
    var write~int_#sizeOfWrittenType : int;
    var glob2_#in~pathlim.offset : int;
    var main_#res : int;
    var write~int_#value : int;
    var __VERIFIER_assert_#in~cond : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    ~tmp~0.offset, ~tmp~0.base := 0, 0;
    havoc main_#res;
    havoc main_#t~ret1, main_~#pathbuf~0.offset, main_~bound~0.base, main_~bound~0.offset, main_~#pathbuf~0.base;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 8;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_~#pathbuf~0.offset, main_~#pathbuf~0.base := #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    main_~bound~0.base, main_~bound~0.offset := main_~#pathbuf~0.base, main_~#pathbuf~0.offset + 4;
    ~tmp~0.offset, ~tmp~0.base := main_~#pathbuf~0.offset + 4, main_~#pathbuf~0.base;
    glob2_#in~pathbuf.base, glob2_#in~pathlim.base, glob2_#in~pathlim.offset, glob2_#in~pathbuf.offset := main_~#pathbuf~0.base, main_~bound~0.base, main_~bound~0.offset, main_~#pathbuf~0.offset;
    havoc glob2_#res;
    havoc glob2_~pathlim.base, glob2_~p~0.offset, glob2_#t~post0.base, glob2_~pathbuf.base, glob2_~pathbuf.offset, glob2_~pathlim.offset, glob2_~p~0.base, glob2_#t~post0.offset;
    glob2_~pathbuf.base, glob2_~pathbuf.offset := glob2_#in~pathbuf.base, glob2_#in~pathbuf.offset;
    glob2_~pathlim.base, glob2_~pathlim.offset := glob2_#in~pathlim.base, glob2_#in~pathlim.offset;
    havoc glob2_~p~0.offset, glob2_~p~0.base;
    glob2_~p~0.offset, glob2_~p~0.base := glob2_~pathbuf.offset, glob2_~pathbuf.base;
    goto loc1;
  loc1:
    assume glob2_~p~0.offset <= glob2_~pathlim.offset && glob2_~pathlim.base == glob2_~p~0.base;
    assume (!(glob2_~p~0.offset <= ~tmp~0.offset) || !(~tmp~0.base == glob2_~p~0.base)) || (~tmp~0.base == glob2_~p~0.base && glob2_~p~0.offset <= ~tmp~0.offset);
    __VERIFIER_assert_#in~cond := (if glob2_~p~0.offset <= ~tmp~0.offset && ~tmp~0.base == glob2_~p~0.base then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume 0 == __VERIFIER_assert_~cond;
    goto loc3;
  loc2_1:
    assume !(0 == __VERIFIER_assert_~cond);
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, glob2_~p~0.base, 1, glob2_~p~0.offset;
    havoc #memory_int;
    assume write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]] == #memory_int;
    glob2_#t~post0.base, glob2_#t~post0.offset := glob2_~p~0.base, glob2_~p~0.offset;
    glob2_~p~0.offset, glob2_~p~0.base := glob2_#t~post0.offset + 4, glob2_#t~post0.base;
    havoc glob2_#t~post0.base, glob2_#t~post0.offset;
    goto loc1;
  loc3:
    assert false;
}

