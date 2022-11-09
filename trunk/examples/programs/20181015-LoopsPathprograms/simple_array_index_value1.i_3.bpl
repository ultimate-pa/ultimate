var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var main_~index~0 : int;
    var #Ultimate.alloc_#res.offset : int;
    var #Ultimate.alloc_~size : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~post1 : int;
    var write~int_old_#memory_int : [int][int]int;
    var main_#t~post0 : int;
    var main_~#array~0.offset : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var write~int_#ptr.offset : int;
    var main_~#array~0.base : int;
    var #in~cond : int;
    var write~int_#sizeOfWrittenType : int;
    var write~int_#ptr.base : int;
    var main_#res : int;
    var main_#t~mem2 : int;
    var write~int_#value : int;
    var main_#t~mem3 : int;
    var #Ultimate.alloc_#res.base : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    havoc main_#res;
    havoc main_~#array~0.base, main_~index~0, main_#t~mem2, main_#t~post1, main_#t~post0, main_~#array~0.offset, main_#t~mem3;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4000;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_~#array~0.base, main_~#array~0.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    havoc main_~index~0;
    main_~index~0 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~index~0 % 4294967296 < 1000);
    main_~index~0 := 0;
    assume main_~index~0 % 4294967296 < 1000;
    assume 0 == (if main_~index~0 % 4294967296 < 0 && !(0 == main_~index~0 % 2) then main_~index~0 % 2 + -2 else main_~index~0 % 2) % 4294967296;
    main_#t~mem2 := #memory_int[main_~#array~0.base][main_~#array~0.offset + 4 * (if main_~index~0 % 4294967296 <= 2147483647 then main_~index~0 % 4294967296 else main_~index~0 % 4294967296 + -4294967296)];
    #in~cond := (if 0 == main_#t~mem2 % 4294967296 then 1 else 0);
    havoc main_#t~mem2;
    goto loc3;
  loc2_1:
    assume main_~index~0 % 4294967296 < 1000;
    write~int_old_#memory_int := #memory_int;
    assume (!(main_~index~0 % 4294967296 < 0) || (!(0 == main_~index~0 % 2) && main_~index~0 % 4294967296 < 0)) || 0 == main_~index~0 % 2;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, main_~#array~0.base, (if main_~index~0 % 4294967296 < 0 && !(0 == main_~index~0 % 2) then main_~index~0 % 2 + -2 else main_~index~0 % 2), main_~#array~0.offset + 4 * (if main_~index~0 % 4294967296 <= 2147483647 then main_~index~0 % 4294967296 else main_~index~0 % 4294967296 + -4294967296);
    havoc #memory_int;
    assume write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]] == #memory_int;
    main_#t~post0 := main_~index~0;
    main_~index~0 := main_#t~post0 + 1;
    havoc main_#t~post0;
    goto loc1;
}

procedure __VERIFIER_assert() returns ()
modifies ;
{
    var #in~cond : int;
    var ~cond : int;

  loc3:
    ~cond := #in~cond;
    assume ~cond == 0;
    goto loc4;
  loc4:
    assert false;
}

