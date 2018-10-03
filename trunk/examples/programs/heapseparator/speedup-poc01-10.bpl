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
  var p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10 : int;

  assume p1 != p2;
  assume p1 != p3;
  assume p1 != p4;
  assume p1 != p5;
  assume p1 != p6;
  assume p1 != p7;
  assume p1 != p8;
  assume p1 != p9;
  assume p1 != p10;

  assume p2 != p3;
  assume p2 != p4;
  assume p2 != p5;
  assume p2 != p6;
  assume p2 != p7;
  assume p2 != p8;
  assume p2 != p9;
  assume p2 != p10;

  assume p3 != p4;
  assume p3 != p5;
  assume p3 != p6;
  assume p3 != p7;
  assume p3 != p8;
  assume p3 != p9;
  assume p3 != p10;

  assume p4 != p5;
  assume p4 != p6;
  assume p4 != p7;
  assume p4 != p8;
  assume p4 != p9;
  assume p4 != p10;

  assume p5 != p6;
  assume p5 != p7;
  assume p5 != p8;
  assume p5 != p9;
  assume p5 != p10;

  assume p6 != p7;
  assume p6 != p8;
  assume p6 != p9;
  assume p6 != p10;

  assume p7 != p8;
  assume p7 != p9;
  assume p7 != p10;

  assume p8 != p9;
  assume p8 != p10;

  assume p9 != p10;

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
    } else {
      #memory_int[p10] := #memory_int[p10] - 1;
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
}
