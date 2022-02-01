var ~array : [int]int;

var ~n : int;

implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~post2 : int;
    var main_#t~post3 : int;
    var main_~array~7 : [int]int;
    var main_~i~7 : int;
    var SelectionSort_#t~post1 : int;
    var SelectionSort_#t~post0 : int;
    var SelectionSort_~lh~4 : int;
    var SelectionSort_~rh~4 : int;
    var SelectionSort_~i~4 : int;
    var SelectionSort_~temp~4 : int;
    var __VERIFIER_assert_#in~cond : int;
    var __VERIFIER_assert_~cond : int;

  loc0:
    ~array := ~array[0 := 0];
    ~array := ~array[1 := 0];
    ~array := ~array[2 := 0];
    ~array := ~array[3 := 0];
    ~array := ~array[4 := 0];
    ~n := 5;
    havoc main_#res;
    havoc main_#t~post2, main_#t~post3, main_~array~7, main_~i~7;
    havoc main_~array~7;
    havoc main_~i~7;
    main_~i~7 := 4;
    goto loc1;
  loc1:
    assume true;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume !(main_~i~7 >= 0);
    havoc SelectionSort_#t~post1, SelectionSort_#t~post0, SelectionSort_~lh~4, SelectionSort_~rh~4, SelectionSort_~i~4, SelectionSort_~temp~4;
    havoc SelectionSort_~lh~4;
    havoc SelectionSort_~rh~4;
    havoc SelectionSort_~i~4;
    havoc SelectionSort_~temp~4;
    SelectionSort_~lh~4 := 0;
    goto loc3;
  loc2_1:
    assume !!(main_~i~7 >= 0);
    main_~array~7 := main_~array~7[main_~i~7 := main_~i~7];
    main_#t~post2 := main_~i~7;
    main_~i~7 := main_#t~post2 - 1;
    havoc main_#t~post2;
    goto loc1;
  loc3:
    assume true;
    goto loc4;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume !(SelectionSort_~lh~4 < ~n);
    main_~i~7 := 0;
    assume true;
    assume !!(main_~i~7 < 5);
    __VERIFIER_assert_#in~cond := (if main_~array~7[main_~i~7] == main_~i~7 then 1 else 0);
    havoc __VERIFIER_assert_~cond;
    __VERIFIER_assert_~cond := __VERIFIER_assert_#in~cond;
    assume __VERIFIER_assert_~cond == 0;
    assume !false;
    goto loc5;
  loc4_1:
    assume !!(SelectionSort_~lh~4 < ~n);
    SelectionSort_~rh~4 := SelectionSort_~lh~4;
    SelectionSort_~i~4 := SelectionSort_~lh~4 + 1;
    goto loc6;
  loc5:
    assert false;
  loc6:
    assume true;
    goto loc7;
  loc7:
    goto loc7_0, loc7_1;
  loc7_0:
    assume !(SelectionSort_~i~4 < ~n);
    SelectionSort_~temp~4 := ~array[SelectionSort_~lh~4];
    ~array := ~array[SelectionSort_~lh~4 := ~array[SelectionSort_~rh~4]];
    ~array := ~array[SelectionSort_~rh~4 := SelectionSort_~temp~4];
    SelectionSort_#t~post0 := SelectionSort_~lh~4;
    SelectionSort_~lh~4 := SelectionSort_#t~post0 + 1;
    havoc SelectionSort_#t~post0;
    goto loc3;
  loc7_1:
    assume !!(SelectionSort_~i~4 < ~n);
    assume ~array[SelectionSort_~i~4] < ~array[SelectionSort_~rh~4];
    SelectionSort_~rh~4 := SelectionSort_~i~4;
    SelectionSort_#t~post1 := SelectionSort_~i~4;
    SelectionSort_~i~4 := SelectionSort_#t~post1 + 1;
    havoc SelectionSort_#t~post1;
    goto loc6;
}

procedure ULTIMATE.start() returns ();
modifies ~array, ~n;
modifies ~array;

