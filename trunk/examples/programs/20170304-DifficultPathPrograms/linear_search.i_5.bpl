var ~SIZE : int;

var #NULL.base : int, #NULL.offset : int;

var #valid : [int]int;

var #length : [int]int;

var #memory_int : [int,int]int;

implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~nondet3 : int;
    var main_#t~ret5 : int;
    var main_~#a~7.base : int, main_~#a~7.offset : int;
    var #Ultimate.alloc_~size : int, #Ultimate.alloc_#res.base : int, #Ultimate.alloc_#res.offset : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var write~int_#value : int, write~int_#ptr.base : int, write~int_#ptr.offset : int, write~int_#sizeOfWrittenType : int;
    var write~int_old_#memory_int : [int,int]int;
    var linear_search_#in~a.base : int, linear_search_#in~a.offset : int;
    var linear_search_#in~n : int;
    var linear_search_#in~q : int;
    var linear_search_#res : int;
    var linear_search_#t~post2 : int;
    var linear_search_#t~mem0 : int;
    var linear_search_#t~short1 : bool;
    var linear_search_~a.base : int, linear_search_~a.offset : int;
    var linear_search_~n : int;
    var linear_search_~q : int;
    var linear_search_~j~5 : int;
    var read~int_#ptr.base : int, read~int_#ptr.offset : int, read~int_#sizeOfReadType : int, read~int_#value : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    #NULL.base, #NULL.offset := 0, 0;
    #valid := #valid[0 := 0];
    ~SIZE := 0;
    havoc main_#res;
    havoc main_#t~nondet3, main_#t~ret5, main_~#a~7.base, main_~#a~7.offset;
    ~SIZE := (if main_#t~nondet3 % 4294967296 < 0 && main_#t~nondet3 % 4294967296 % 2 != 0 then main_#t~nondet3 % 4294967296 / 2 + 1 else main_#t~nondet3 % 4294967296 / 2) + 1;
    havoc main_#t~nondet3;
    #Ultimate.alloc_old_#length, #Ultimate.alloc_old_#valid := #length, #valid;
    #Ultimate.alloc_~size := ~SIZE % 4294967296 * 4;
    havoc #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    havoc #valid, #length;
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base] == 0;
    assume #valid == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1];
    assume #Ultimate.alloc_#res.offset == 0;
    assume #Ultimate.alloc_#res.base != 0;
    assume #length == #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size];
    main_~#a~7.base, main_~#a~7.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    write~int_old_#memory_int := #memory_int;
    write~int_#value, write~int_#ptr.base, write~int_#ptr.offset, write~int_#sizeOfWrittenType := 3, main_~#a~7.base, main_~#a~7.offset + (if ~SIZE % 4294967296 < 0 && ~SIZE % 4294967296 % 2 != 0 then ~SIZE % 4294967296 / 2 + 1 else ~SIZE % 4294967296 / 2) % 4294967296 * 4, 4;
    havoc #memory_int;
    assume #memory_int == write~int_old_#memory_int[write~int_#ptr.base,write~int_#ptr.offset := write~int_#value];
    linear_search_#in~a.base, linear_search_#in~a.offset, linear_search_#in~n, linear_search_#in~q := main_~#a~7.base, main_~#a~7.offset, (if ~SIZE % 4294967296 % 4294967296 <= 2147483647 then ~SIZE % 4294967296 % 4294967296 else ~SIZE % 4294967296 % 4294967296 - 4294967296), 3;
    havoc linear_search_#res;
    havoc linear_search_#t~post2, linear_search_#t~mem0, linear_search_#t~short1, linear_search_~a.base, linear_search_~a.offset, linear_search_~n, linear_search_~q, linear_search_~j~5;
    linear_search_~a.base, linear_search_~a.offset := linear_search_#in~a.base, linear_search_#in~a.offset;
    linear_search_~n := linear_search_#in~n;
    linear_search_~q := linear_search_#in~q;
    linear_search_~j~5 := 0;
    goto loc1;
  loc1:
    assume true;
    linear_search_#t~short1 := linear_search_~j~5 % 4294967296 < linear_search_~n % 4294967296;
    assume linear_search_#t~short1;
    read~int_#ptr.base, read~int_#ptr.offset, read~int_#sizeOfReadType := linear_search_~a.base, linear_search_~a.offset + linear_search_~j~5 % 4294967296 * 4, 4;
    havoc read~int_#value;
    assume read~int_#value == #memory_int[read~int_#ptr.base,read~int_#ptr.offset];
    linear_search_#t~mem0 := read~int_#value;
    linear_search_#t~short1 := linear_search_#t~mem0 != linear_search_~q;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !linear_search_#t~short1;
    havoc linear_search_#t~mem0;
    havoc linear_search_#t~short1;
    assume !(linear_search_~j~5 % 4294967296 < ~SIZE % 4294967296);
    linear_search_#res := 0;
    main_#t~ret5 := linear_search_#res;
    assume -2147483648 <= main_#t~ret5 && main_#t~ret5 <= 2147483647;
    __VERIFIER_assert_#in~cond := main_#t~ret5;
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc3;
  loc2_1:
    assume !!linear_search_#t~short1;
    havoc linear_search_#t~mem0;
    havoc linear_search_#t~short1;
    linear_search_#t~post2 := linear_search_~j~5;
    linear_search_~j~5 := linear_search_#t~post2 + 1;
    havoc linear_search_#t~post2;
    assume !(linear_search_~j~5 % 4294967296 == 20);
    goto loc1;
  loc3:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies #valid, #NULL.base, #NULL.offset, ~SIZE, ~SIZE, #memory_int;
modifies #valid, #length, ~SIZE, #memory_int;

