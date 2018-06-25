var #memory_int1, #memory_int2, #valid : [int] int;

procedure ULTIMATE.start(); 
modifies #memory_int1, #memory_int2, #valid;

implementation ULTIMATE.start() {
  var p1, p2, x1, x2 : int;

  assume p1 != p2;

  #memory_int1[p1] := 0;
  #memory_int2[p2] := 0;

  while (*) {
    if (*) {
      #memory_int1[p1] := #memory_int1[p1] + 1;
    } else {
      #memory_int2[p2] := #memory_int2[p2] - 1;
    }
  }
  assert #memory_int1[p1] >= 0;
  assert #memory_int2[p2] <= 0;

}
