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
  var p1, p2, p3, p4 : int;

  call p1 := malloc();
  call p2 := malloc();
  call p3 := malloc();
  call p4 := malloc();

  #memory_int[p1] := 0;
  #memory_int[p2] := 0;
  #memory_int[p3] := 0;
  #memory_int[p4] := 0;

  while (*) {
    if (*) {
      call p1 := malloc();
      #memory_int[p1] := 0;
    }
    if (*) {
      call p2 := malloc();
      #memory_int[p2] := 0;
    }
    if (*) {
      call p3 := malloc();
      #memory_int[p3] := 0;
    }
    if (*) {
      call p4 := malloc();
      #memory_int[p4] := 0;
    }

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

procedure malloc() returns (ptr : int);
modifies #valid;
ensures old(#valid)[ptr] == 0;
ensures #valid == old(#valid)[ptr:=1];
  
