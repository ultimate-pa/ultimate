//#Safe
var a, b : [int] int;

procedure main();
modifies a;

implementation main() {
  var i : int;

  assume b[i] == 0;
  a[i] := 7;

  call foo();

  assert a[i] == 7;
}

procedure foo();
modifies a;

implementation foo() {
  var j : int;
  assume b[j] == 1;
  a[j] := 13;
  havoc j;
}
