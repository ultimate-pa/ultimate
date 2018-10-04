
//#Safe
var #memory_int, #valid : [int] int;

procedure ULTIMATE.start(); 
modifies #memory_int, #valid;

implementation ULTIMATE.start() {
  // heap separator expects the initial edge to be a Call, that's the only 
  // reason to have a second procedure here
  call main();
}

procedure main(); 
modifies #memory_int, #valid;

implementation main() {
  var p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18 : int;

  call p1 := malloc();
  call p2 := malloc();
  call p3 := malloc();
  call p4 := malloc();
  call p5 := malloc();
  call p6 := malloc();
  call p7 := malloc();
  call p8 := malloc();
  call p9 := malloc();
  call p10 := malloc();
  call p11 := malloc();
  call p12 := malloc();
  call p13 := malloc();
  call p14 := malloc();
  call p15 := malloc();
  call p16 := malloc();
  call p17 := malloc();
  call p18 := malloc();

  #memory_int[p1] := 0;
  #memory_int[p2] := 0;
  #memory_int[p3] := 0;
  #memory_int[p4] := 0;
  #memory_int[p5] := 0;
  #memory_int[p6] := 0;
  #memory_int[p7] := 0;
  #memory_int[p8] := 0;
  #memory_int[p9] := 0;
  #memory_int[p10] := 0;
  #memory_int[p11] := 0;
  #memory_int[p12] := 0;
  #memory_int[p13] := 0;
  #memory_int[p14] := 0;
  #memory_int[p15] := 0;
  #memory_int[p16] := 0;
  #memory_int[p17] := 0;
  #memory_int[p18] := 0;

  while (*) {
    if (*) {
      #memory_int[p1] := #memory_int[p1] + 1;
    } else if (*) {
      #memory_int[p2] := #memory_int[p2] - 1;
    } else if (*) {
      #memory_int[p3] := #memory_int[p3] + 1;
    } else if (*) {
      #memory_int[p4] := #memory_int[p4] - 1;
    } else if (*) {
      #memory_int[p5] := #memory_int[p5] + 1;
    } else if (*) {
      #memory_int[p6] := #memory_int[p6] - 1;
    } else if (*) {
      #memory_int[p7] := #memory_int[p7] + 1;
    } else if (*) {
      #memory_int[p8] := #memory_int[p8] - 1;
    } else if (*) {
      #memory_int[p9] := #memory_int[p9] + 1;
    } else if (*) {
      #memory_int[p10] := #memory_int[p10] - 1;
    } else if (*) {
      #memory_int[p11] := #memory_int[p11] + 1;
    } else if (*) {
      #memory_int[p12] := #memory_int[p12] - 1;
    } else if (*) {
      #memory_int[p13] := #memory_int[p13] + 1;
    } else if (*) {
      #memory_int[p14] := #memory_int[p14] - 1;
    } else if (*) {
      #memory_int[p15] := #memory_int[p15] + 1;
    } else if (*) {
      #memory_int[p16] := #memory_int[p16] - 1;
    } else if (*) {
      #memory_int[p17] := #memory_int[p17] + 1;
    } else {
      #memory_int[p18] := #memory_int[p18] - 1;
    }
  }
  assert #memory_int[p1] >= 0;
  assert #memory_int[p2] <= 0;
  assert #memory_int[p3] >= 0;
  assert #memory_int[p4] <= 0;
  assert #memory_int[p5] >= 0;
  assert #memory_int[p6] <= 0;
  assert #memory_int[p7] >= 0;
  assert #memory_int[p8] <= 0;
  assert #memory_int[p9] >= 0;
  assert #memory_int[p10] <= 0;
  assert #memory_int[p11] >= 0;
  assert #memory_int[p12] <= 0;
  assert #memory_int[p13] >= 0;
  assert #memory_int[p14] <= 0;
  assert #memory_int[p15] >= 0;
  assert #memory_int[p16] <= 0;
  assert #memory_int[p17] >= 0;
  assert #memory_int[p18] <= 0;
}

procedure malloc() returns (ptr : int);
modifies #valid;
ensures old(#valid)[ptr] == 0;
ensures #valid == old(#valid)[ptr:=1];
  
