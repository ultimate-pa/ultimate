//#Safe
var #memory_int, #valid : [int] int;

procedure ULTIMATE.start();
modifies #memory_int, #valid;

implementation ULTIMATE.start() {
  call main();
}

procedure main();
modifies #memory_int, #valid;

implementation main() {
  var p1, p2, p3, p4, p5, p6 : int;

  call p1 := malloc();
  call p2 := malloc();
  call p3 := malloc();
  call p4 := malloc();
  call p5 := malloc();
  call p6 := malloc();

  assume p1 < p2;
  assume p2 < p3;
  assume p3 < p4;
  assume p4 < p5;
  assume p5 < p6;

  #memory_int[p1] := 0;
  #memory_int[p2] := 0;
  #memory_int[p3] := 0;
  #memory_int[p4] := 0;
  #memory_int[p5] := 0;
  #memory_int[p6] := 0;

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
    } else {
      #memory_int[p6] := #memory_int[p6] - 1;
    }
  }

  assert #memory_int[p1] >= 0;
  assert #memory_int[p2] <= 0;
  assert #memory_int[p3] >= 0;
  assert #memory_int[p4] <= 0;
  assert #memory_int[p5] >= 0;
  assert #memory_int[p6] <= 0;

}

procedure malloc() returns (ptr : int);
modifies #valid;
ensures old(#valid)[ptr] == 0;
ensures #valid == old(#valid)[ptr:=1];
