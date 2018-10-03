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
  var p1, p2, x1, x2 : int;

  p1 := 1;
  p2 := 2;

  #memory_int[p1] := 0;
  #memory_int[p2] := 0;

  while (*) {
    if (*) {
      #memory_int[p1] := #memory_int[p1] + 1;
    } else {
      #memory_int[p2] := #memory_int[p2] - 1;
    }
  }
  assert #memory_int[p1] >= 0;
  assert #memory_int[p2] <= 0;

}
