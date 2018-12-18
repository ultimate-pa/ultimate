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
  var p1 : int;

  call p1 := malloc();

  #memory_int[p1] := 0;

  while (*) {
      #memory_int[p1] := #memory_int[p1] + 1;

  }

  assert #memory_int[p1] <= 0;

}

procedure malloc() returns (ptr : int);
modifies #valid;
ensures old(#valid)[ptr] == 0;
ensures #valid == old(#valid)[ptr:=1];
