var #valid : [int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #NULL.offset, #length, #NULL.base;
{
    var #Ultimate.alloc_#res.offset : int;
    var #Ultimate.alloc_~size : int;
    var main_#t~memset3.base : int;
    var #Ultimate.C_memset_#amount : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var ULTIMATE.dealloc_~addr.offset : int;
    var main_#t~memset3.offset : int;
    var #Ultimate.C_memset_#ptr.offset : int;
    var #Ultimate.C_memset_#t~loopctr5 : int;
    var ULTIMATE.dealloc_old_#valid : [int]int;
    var #Ultimate.C_memset_#value : int;
    var main_~#cstats~0.base : int;
    var main_#res : int;
    var #Ultimate.C_memset_#ptr.base : int;
    var #Ultimate.C_memset_#res.base : int;
    var #Ultimate.C_memset_#res.offset : int;
    var ULTIMATE.dealloc_~addr.base : int;
    var main_~#cstats~0.offset : int;
    var #Ultimate.alloc_#res.base : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_#t~memset3.offset, main_#t~memset3.base, main_~#cstats~0.base, main_~#cstats~0.offset;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 40;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_~#cstats~0.base, main_~#cstats~0.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    #Ultimate.C_memset_#ptr.offset, #Ultimate.C_memset_#value, #Ultimate.C_memset_#amount, #Ultimate.C_memset_#ptr.base := main_~#cstats~0.offset, 10, 40, main_~#cstats~0.base;
    assume #valid[#Ultimate.C_memset_#ptr.base] == 1;
    assume 0 <= #Ultimate.C_memset_#ptr.offset && #Ultimate.C_memset_#ptr.offset + #Ultimate.C_memset_#amount <= #length[#Ultimate.C_memset_#ptr.base];
    assume #valid[#Ultimate.C_memset_#ptr.base] == 1;
    assume 0 <= #Ultimate.C_memset_#ptr.offset && #Ultimate.C_memset_#amount + #Ultimate.C_memset_#ptr.offset <= #length[#Ultimate.C_memset_#ptr.base];
    havoc #Ultimate.C_memset_#res.base, #Ultimate.C_memset_#res.offset;
    havoc #Ultimate.C_memset_#t~loopctr5;
    #Ultimate.C_memset_#t~loopctr5 := 0;
    goto loc1;
  loc1:
    goto loc1_0, loc1_1;
  loc1_0:
    assume #Ultimate.C_memset_#t~loopctr5 < #Ultimate.C_memset_#amount;
    #Ultimate.C_memset_#t~loopctr5 := #Ultimate.C_memset_#t~loopctr5 + 1;
    goto loc1;
  loc1_1:
    assume !(#Ultimate.C_memset_#t~loopctr5 < #Ultimate.C_memset_#amount);
    assume #Ultimate.C_memset_#ptr.base == #Ultimate.C_memset_#res.base && #Ultimate.C_memset_#ptr.offset == #Ultimate.C_memset_#res.offset;
    main_#t~memset3.offset, main_#t~memset3.base := #Ultimate.C_memset_#res.offset, #Ultimate.C_memset_#res.base;
    havoc main_#t~memset3.offset, main_#t~memset3.base;
    main_#res := 0;
    ULTIMATE.dealloc_old_#valid := #valid;
    ULTIMATE.dealloc_~addr.base, ULTIMATE.dealloc_~addr.offset := main_~#cstats~0.base, main_~#cstats~0.offset;
    havoc #valid;
    assume #valid == ULTIMATE.dealloc_old_#valid[ULTIMATE.dealloc_~addr.base := 0];
    havoc main_~#cstats~0.base, main_~#cstats~0.offset;
    assume !(main_old_#valid == #valid);
    goto loc2;
  loc2:
    assert false;
}

