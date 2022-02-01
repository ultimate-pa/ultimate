//#Safe

procedure foo() {
  var a, b, c, mixed1, mixed2 : [int] int;
  var nondet : [int] bool;
  var i, j, k : int;

  a := ~const~Array~Int~Int(0);
  b := ~const~Array~Int~Int(1);
  //c := ~const~Array~Int~Int(2);

  a[j] := 2;

  // havoc nondet;
  mixed1 := ~mix~Array~Int~Int(a, b, nondet);

  mixed1[k] := 3;

  assert mixed1[i] == 0 || mixed1[i] == 1 || mixed1[i] == 2 || mixed1[i] == 3;

  //havoc nondet;
  //mixed2 := ~mix~Array~Int~Int(mixed1, c, nondet);

  //assert mixed2[i] == 0 || mixed2[i] == 1 || mixed2[i] == 2;
}

function { :builtin "const-Array-Int-Int" } ~const~Array~Int~Int(in : int) returns (out : [int] int);

function { :builtin "mix-Array-Int-Int" } ~mix~Array~Int~Int(in1 : [int] int, in2 : [int] int, nondet : [int] bool) returns (out : [int] int);

