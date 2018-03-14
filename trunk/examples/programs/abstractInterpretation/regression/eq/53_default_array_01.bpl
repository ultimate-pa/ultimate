//#Safe
procedure foo() {
  var a : [int] int;
  var i : int;

  //assert @0[i] == 0;

  a := ~defaultArray~0();

  assert a[i] == 0;
}

function { :builtin "@0" } ~defaultArray~0() returns (out : [int] int);
