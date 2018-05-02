//#Safe
procedure foo() {
  var a, b, mixed : [int] int;
  var nondet : [int] bool;
  var i : int;

  a := ~const~Array~Int~Int(0);
  b := ~const~Array~Int~Int(1);

  havoc nondet;
  mixed := ~mix~Array~Int~Int(a, b, nondet);

  assert mixed[i] == 0 || mixed [i] == 1;
}

function { :builtin "const-Array-Int-Int" } ~const~Array~Int~Int(in : int) returns (out : [int] int);

function { :builtin "mix-Array-Int-Int" } ~mix~Array~Int~Int(in1 : [int] int, in2 : [int] int, nondet : [int] bool) returns (out : [int] int);

