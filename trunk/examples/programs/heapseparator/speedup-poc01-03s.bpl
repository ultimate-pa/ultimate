//#Safe
var #memory_int_1, #memory_int_2, #memory_int_3, #memory_int_4, #valid : [int] int;

procedure ULTIMATE.start(); 
modifies #memory_int_1, #memory_int_2, #memory_int_3, #memory_int_4, #valid;

implementation ULTIMATE.start() {
  var p1, p2, p3, p4, x1, x2, x3, x4 : int;

  assume p1 != p2;
  assume p1 != p3;
  assume p1 != p4;
  assume p2 != p3;
  assume p2 != p4;
  assume p3 != p4;

  #memory_int_1[p1] := 0;
  #memory_int_2[p2] := 0;
  #memory_int_3[p3] := 0;
  #memory_int_4[p4] := 0;

  while (*) {
    if (*) {
      #memory_int_1[p1] := #memory_int_1[p1] + 1;
    } else if (*) {
      #memory_int_2[p2] := #memory_int_2[p2] - 1;
    } else if (*) {
      #memory_int_3[p3] := #memory_int_3[p3] + 1;
    } else {
      #memory_int_4[p4] := #memory_int_4[p4] - 1;
    }
  }
  assert #memory_int_1[p1] >= 0;
  assert #memory_int_2[p2] <= 0;
  assert #memory_int_3[p3] >= 0;
  assert #memory_int_4[p4] <= 0;

}
