var #valid : [int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #NULL.offset, #length, #NULL.base;
{
    var main_#t~post10 : int;
    var main_#t~nondet1 : int;
    var #Ultimate.alloc_#res.offset : int;
    var #Ultimate.alloc_~size : int;
    var main_#t~nondet2 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_~#array~0.offset : int;
    var main_#t~post6 : int;
    var main_#t~post5 : int;
    var #Ultimate.alloc_old_#length : [int]int;
    var main_~#array~0.base : int;
    var main_#t~mem8 : int;
    var main_#t~post9 : int;
    var #in~cond : int;
    var main_#t~mem7 : int;
    var main_#res : int;
    var main_~index2~0 : int;
    var main_~index1~0 : int;
    var main_#t~mem4 : int;
    var main_~loop_entered~0 : int;
    var main_#t~mem3 : int;
    var #Ultimate.alloc_#res.base : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    havoc main_#res;
    havoc main_#t~post10, main_#t~nondet1, main_#t~nondet2, main_~#array~0.offset, main_#t~post6, main_#t~post5, main_~#array~0.base, main_#t~mem8, main_#t~post9, main_#t~mem7, main_~index2~0, main_~index1~0, main_#t~mem4, main_~loop_entered~0, main_#t~mem3;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 400000;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_~#array~0.base, main_~#array~0.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    havoc main_~index1~0;
    havoc main_~index2~0;
    main_~loop_entered~0 := 0;
    main_~index1~0 := main_#t~nondet1;
    havoc main_#t~nondet1;
    assume main_~index1~0 % 4294967296 < 100000;
    main_~index2~0 := main_#t~nondet2;
    havoc main_#t~nondet2;
    assume main_~index2~0 % 4294967296 < 100000;
    goto loc1;
  loc1:
    assume main_~index1~0 % 4294967296 < main_~index2~0 % 4294967296;
    assume (!(main_~index2~0 % 4294967296 < 100000) || !(main_~index1~0 % 4294967296 < 100000)) || (main_~index1~0 % 4294967296 < 100000 && main_~index2~0 % 4294967296 < 100000);
    #in~cond := (if main_~index2~0 % 4294967296 < 100000 && main_~index1~0 % 4294967296 < 100000 then 1 else 0);
    havoc main_~index2~0, main_~index1~0;
    goto loc2;
}

procedure __VERIFIER_assert() returns ()
modifies ;
{
    var #in~cond : int;
    var ~cond : int;

  loc2:
    ~cond := #in~cond;
    goto loc3;
  loc3:
    goto loc3_0, loc3_1;
  loc3_0:
    assume ~cond == 0;
    goto loc4;
  loc3_1:
    assume !(~cond == 0);
    return;
  loc4:
    assert false;
}

