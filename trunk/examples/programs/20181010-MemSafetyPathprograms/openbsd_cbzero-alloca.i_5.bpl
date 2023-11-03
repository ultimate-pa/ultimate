var #valid : [int]int;

var #memory_int : [int][int]int;

var #NULL.offset : int;

var #length : [int]int;

var #NULL.base : int;

procedure ULTIMATE.start() returns ()
modifies #valid, #memory_int, #NULL.offset, #length, #NULL.base;
{
    var main_~nondetArea~0.offset : int;
    var cbzero_#t~post3.offset : int;
    var main_#t~nondet4 : int;
    var main_#t~nondet5 : int;
    var cbzero_#in~b.offset : int;
    var cbzero_~b.base : int;
    var main_~nondetArea~0.base : int;
    var #Ultimate.alloc_old_#valid : [int]int;
    var cbzero_#t~post3.base : int;
    var write~int_#ptr.offset : int;
    var cbzero_#t~post2 : int;
    var cbzero_~p~0.base : int;
    var cbzero_~p~0.offset : int;
    var write~int_#ptr.base : int;
    var main_#t~malloc6.offset : int;
    var cbzero_#in~b.base : int;
    var #Ultimate.alloc_#res.base : int;
    var #Ultimate.alloc_#res.offset : int;
    var #Ultimate.alloc_~size : int;
    var main_#t~malloc6.base : int;
    var main_~n~0 : int;
    var write~int_old_#memory_int : [int][int]int;
    var main_old_#valid : [int]int;
    var #Ultimate.alloc_old_#length : [int]int;
    var write~int_#sizeOfWrittenType : int;
    var cbzero_~length : int;
    var main_#res : int;
    var cbzero_~b.offset : int;
    var write~int_#value : int;
    var cbzero_#in~length : int;
    var main_~length~0 : int;

  loc0:
    #NULL.offset, #NULL.base := 0, 0;
    #valid := #valid[0 := 0];
    main_old_#valid := #valid;
    havoc main_#res;
    havoc main_~nondetArea~0.offset, main_#t~nondet4, main_#t~malloc6.base, main_#t~nondet5, main_#t~malloc6.offset, main_~n~0, main_~nondetArea~0.base, main_~length~0;
    assume main_#t~nondet4 <= 2147483647 && 0 <= main_#t~nondet4 + 2147483648;
    main_~length~0 := main_#t~nondet4;
    havoc main_#t~nondet4;
    assume main_#t~nondet5 <= 2147483647 && 0 <= main_#t~nondet5 + 2147483648;
    main_~n~0 := main_#t~nondet5;
    havoc main_#t~nondet5;
    assume !(main_~length~0 < 1);
    assume !(main_~n~0 < 1);
    assume !(main_~length~0 < main_~n~0);
    #Ultimate.alloc_old_#valid, #Ultimate.alloc_old_#length := #valid, #length;
    #Ultimate.alloc_~size := main_~length~0;
    havoc #Ultimate.alloc_#res.offset, #Ultimate.alloc_#res.base;
    havoc #valid, #length;
    assume 0 == #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base];
    assume #Ultimate.alloc_old_#valid[#Ultimate.alloc_#res.base := 1] == #valid;
    assume #Ultimate.alloc_#res.offset == 0;
    assume !(0 == #Ultimate.alloc_#res.base);
    assume #Ultimate.alloc_old_#length[#Ultimate.alloc_#res.base := #Ultimate.alloc_~size] == #length;
    main_#t~malloc6.base, main_#t~malloc6.offset := #Ultimate.alloc_#res.base, #Ultimate.alloc_#res.offset;
    main_~nondetArea~0.offset, main_~nondetArea~0.base := main_#t~malloc6.offset, main_#t~malloc6.base;
    cbzero_#in~b.offset, cbzero_#in~length, cbzero_#in~b.base := main_~nondetArea~0.offset, main_~n~0, main_~nondetArea~0.base;
    havoc cbzero_~p~0.base, cbzero_~p~0.offset, cbzero_#t~post3.offset, cbzero_~length, cbzero_~b.base, cbzero_~b.offset, cbzero_#t~post3.base, cbzero_#t~post2;
    cbzero_~b.base, cbzero_~b.offset := cbzero_#in~b.base, cbzero_#in~b.offset;
    cbzero_~length := cbzero_#in~length;
    havoc cbzero_~p~0.base, cbzero_~p~0.offset;
    cbzero_~p~0.base, cbzero_~p~0.offset := cbzero_~b.base, cbzero_~b.offset;
    goto loc1;
  loc1:
    cbzero_#t~post2 := cbzero_~length;
    cbzero_~length := cbzero_#t~post2 + -1;
    assume !(cbzero_#t~post2 % 4294967296 == 0);
    havoc cbzero_#t~post2;
    cbzero_#t~post3.offset, cbzero_#t~post3.base := cbzero_~p~0.offset, cbzero_~p~0.base;
    cbzero_~p~0.base, cbzero_~p~0.offset := cbzero_#t~post3.base, cbzero_#t~post3.offset + 1;
    write~int_old_#memory_int := #memory_int;
    write~int_#sizeOfWrittenType, write~int_#ptr.base, write~int_#value, write~int_#ptr.offset := 1, cbzero_#t~post3.base, 0, cbzero_#t~post3.offset;
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
    havoc cbzero_#t~post3.offset, cbzero_#t~post3.base;
    goto loc1;
  loc3:
    assert false;
}

