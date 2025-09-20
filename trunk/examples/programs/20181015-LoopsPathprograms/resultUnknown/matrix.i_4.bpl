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
    var main_#t~nondet3 : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var main_#t~post2 : int;
    var main_#t~post1 : int;
    var main_~N_LIN~0 : int;
    var write~int_#ptr.offset : int;
    var write~int_#ptr.base : int;
    var main_~j~0 : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var #Ultimate.alloc_~size : int;
    var write~int_old_#memory_int : [int][int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var main_~#matriz~0.offset : int;
    var write~int_#sizeOfWrittenType : int;
    var main_~N_COL~0 : int;
    var main_#res : int;
    var main_~maior~0 : int;
    var write~int_#value : int;
    var main_~#matriz~0.base : int;
    var __VERIFIER_assert_#in~cond : int;
    var main_#t~mem6 : int;
    var main_#t~mem5 : int;
    var main_#t~mem4 : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    havoc main_#res;
    havoc main_#t~nondet0, main_~k~0, main_#t~nondet3, main_#t~post2, main_#t~post1, main_~N_LIN~0, main_~#matriz~0.offset, main_~N_COL~0, main_~j~0, main_~maior~0, main_~#matriz~0.base, main_#t~mem6, main_#t~mem5, main_#t~mem4;
    main_~N_LIN~0 := 1;
    main_~N_COL~0 := 1;
    havoc main_~j~0;
    havoc main_~k~0;
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := 4 * (if main_~N_LIN~0 % 4294967296 <= 2147483647 then main_~N_LIN~0 % 4294967296 else main_~N_LIN~0 % 4294967296 + -4294967296) * (if main_~N_COL~0 % 4294967296 <= 2147483647 then main_~N_COL~0 % 4294967296 else main_~N_COL~0 % 4294967296 + -4294967296);
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_~#matriz~0.offset, main_~#matriz~0.base := #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc main_~maior~0;
    assume 0 <= main_#t~nondet0 + 2147483648 && main_#t~nondet0 <= 2147483647;
    main_~maior~0 := main_#t~nondet0;
    havoc main_#t~nondet0;
    main_~j~0 := 0;
    goto loc1;
  loc1:
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~j~0 % 4294967296 < main_~N_COL~0 % 4294967296);
    main_#t~mem6 := #memory_int[main_~#matriz~0.base][main_~#matriz~0.offset];
    __VERIFIER_assert_#in~cond := (if main_#t~mem6 <= main_~maior~0 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume 0 == __VERIFIER_assert_~cond;
    goto loc3;
  loc2_1:
    assume main_~j~0 % 4294967296 < main_~N_COL~0 % 4294967296;
    main_~k~0 := 0;
    goto loc4;
  loc3:
    assert false;
  loc4:
    goto loc5;
  loc5:
    goto loc5_0, loc5_1;
  loc5_0:
    assume !(main_~k~0 % 4294967296 < main_~N_LIN~0 % 4294967296);
    main_#t~post1 := main_~j~0;
    main_~j~0 := main_#t~post1 + 1;
    havoc main_#t~post1;
    goto loc1;
  loc5_1:
    assume main_~k~0 % 4294967296 < main_~N_LIN~0 % 4294967296;
    assume 0 <= main_#t~nondet3 + 2147483648 && main_#t~nondet3 <= 2147483647;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 4, main_~#matriz~0.base, main_#t~nondet3, main_~#matriz~0.offset + (if main_~j~0 % 4294967296 <= 2147483647 then main_~j~0 % 4294967296 else main_~j~0 % 4294967296 + -4294967296) * (4 * (if main_~N_LIN~0 % 4294967296 <= 2147483647 then main_~N_LIN~0 % 4294967296 else main_~N_LIN~0 % 4294967296 + -4294967296)) + 4 * (if main_~k~0 % 4294967296 <= 2147483647 then main_~k~0 % 4294967296 else main_~k~0 % 4294967296 + -4294967296);
    havoc #memory_int;
    assume write~int_old_#memory_int[write~int_#ptr.base := write~int_old_#memory_int[write~int_#ptr.base][write~int_#ptr.offset := write~int_#value]] == #memory_int;
    havoc main_#t~nondet3;
    main_#t~mem4 := #memory_int[main_~#matriz~0.base][main_~#matriz~0.offset + (if main_~j~0 % 4294967296 <= 2147483647 then main_~j~0 % 4294967296 else main_~j~0 % 4294967296 + -4294967296) * (4 * (if main_~N_LIN~0 % 4294967296 <= 2147483647 then main_~N_LIN~0 % 4294967296 else main_~N_LIN~0 % 4294967296 + -4294967296)) + 4 * (if main_~k~0 % 4294967296 <= 2147483647 then main_~k~0 % 4294967296 else main_~k~0 % 4294967296 + -4294967296)];
    assume !(main_~maior~0 <= main_#t~mem4);
    havoc main_#t~mem4;
    main_#t~post2 := main_~k~0;
    main_~k~0 := main_#t~post2 + 1;
    havoc main_#t~post2;
    goto loc4;
}

