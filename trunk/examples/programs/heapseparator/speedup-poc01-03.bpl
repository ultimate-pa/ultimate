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
  var p1, p2, p3, p4, x1, x2, x3, x4 : int;

  assume p1 != p2;
  assume p1 != p3;
  assume p1 != p4;
  assume p2 != p3;
  assume p2 != p4;
  assume p3 != p4;

  #memory_int[p1] := 0;
  #memory_int[p2] := 0;
  #memory_int[p3] := 0;
  #memory_int[p4] := 0;

  while (*) {
    if (*) {
      #memory_int[p1] := #memory_int[p1] + 1;
    } else if (*) {
      #memory_int[p2] := #memory_int[p2] - 1;
    } else if (*) {
      #memory_int[p3] := #memory_int[p3] + 1;
    } else {
      #memory_int[p4] := #memory_int[p4] - 1;
    }
  }
  assert #memory_int[p1] >= 0;
  assert #memory_int[p2] <= 0;
  assert #memory_int[p3] >= 0;
  assert #memory_int[p4] <= 0;

}
