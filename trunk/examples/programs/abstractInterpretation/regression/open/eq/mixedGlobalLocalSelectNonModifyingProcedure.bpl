var a : [int] int;

procedure main ();
modifies a;

implementation main () {
  var x, y : int;

  a[x] := 3;
  
  call y := foo(x);

  assert a[x] == 3;
}

procedure foo(y : int) returns (res : int);
modifies;

implementation foo(y : int) returns (res : int) {
  res := y;
  return;
}

