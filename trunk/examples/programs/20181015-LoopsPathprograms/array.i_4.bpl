var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var main_#t~nondet0 : int;
    var main_~k~0 : int;
    var __VERIFIER_assert_~cond : int;
    var main_#t~nondet2 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~post1 : int;
    var main_~#array~0.offset : int;
    var write~int_#ptr.offset : int;
    var main_~#array~0.base : int;
    var write~int_#ptr.base : int;
    var main_~j~0 : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var #Ultimate.alloc_~size : int;
    var write~int_old_#memory_int : [int][int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var write~int_#sizeOfWrittenType : int;
    var main_#res : int;
    var main_~menor~0 : int;
    var write~int_#value : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_~SIZE~0 : int;
    var main_#t~mem5 : int;
    var main_#t~mem4 : int;
    var main_#t~mem3 : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    havoc main_#res;
    havoc main_#t~nondet0, main_~k~0, main_~#array~0.base, main_~j~0, main_#t~nondet2, main_~menor~0, main_#t~post1, main_~#array~0.offset, main_~SIZE~0, main_#t~mem5, main_#t~mem4, main_#t~mem3;
    main_~SIZE~0 := 1;
    havoc main_~j~0;
    havoc main_~k~0;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4 * (if main_~SIZE~0 % 4294967296 <= 2147483647 then main_~SIZE~0 % 4294967296 else main_~SIZE~0 % 4294967296 + -4294967296);
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_~#array~0.base, main_~#array~0.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    havoc main_~menor~0;
    assume 0 <= main_#t~nondet0 + 2147483648 && main_#t~nondet0 <= 2147483647;
    main_~menor~0 := main_#t~nondet0;
    havoc main_#t~nondet0;
    main_~j~0 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~j~0 % 4294967296 < main_~SIZE~0 % 4294967296);
    main_#t~mem5 := #memory_int[main_~#array~0.base][main_~#array~0.offset];
    __VERIFIER_assert_#in~cond := (if main_~menor~0 <= main_#t~mem5 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume 0 == __VERIFIER_assert_~cond;
    goto loc3;
  loc2_1:
    assume main_~j~0 % 4294967296 < main_~SIZE~0 % 4294967296;
    assume 0 <= main_#t~nondet2 + 2147483648 && main_#t~nondet2 <= 2147483647;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, main_~#array~0.base, main_#t~nondet2, 4 * (if main_~j~0 % 4294967296 <= 2147483647 then main_~j~0 % 4294967296 else main_~j~0 % 4294967296 + -4294967296) + main_~#array~0.offset;
    havoc #memory_int;
    assume write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]] == #memory_int;
    havoc main_#t~nondet2;
    main_#t~mem3 := #memory_int[main_~#array~0.base][4 * (if main_~j~0 % 4294967296 <= 2147483647 then main_~j~0 % 4294967296 else main_~j~0 % 4294967296 + -4294967296) + main_~#array~0.offset];
    assume main_#t~mem3 <= main_~menor~0;
    havoc main_#t~mem3;
    main_#t~mem4 := #memory_int[main_~#array~0.base][4 * (if main_~j~0 % 4294967296 <= 2147483647 then main_~j~0 % 4294967296 else main_~j~0 % 4294967296 + -4294967296) + main_~#array~0.offset];
    main_~menor~0 := main_#t~mem4;
    havoc main_#t~mem4;
    main_#t~post1 := main_~j~0;
    main_~j~0 := main_#t~post1 + 1;
    havoc main_#t~post1;
    goto loc1;
  loc3:
    assert false;
}

