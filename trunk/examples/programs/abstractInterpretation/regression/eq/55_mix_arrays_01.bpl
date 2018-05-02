//#Safe
/*
 * Note that we currently cannot handle this test case because we require all 
 *  set constraints to be only about literals.
 */
procedure foo() {
  var a, b, mixed : [int] int;
  var nondet : [int] bool;
  var i : int;

  mixed := ~mix~Array~Int~Int(a, b, nondet);

  assert mixed[i] == a[i] || mixed[i] == b[i];
}

function { :builtin "mix-Array-Int-Int" } ~mix~Array~Int~Int(in1 : [int] int, in2 : [int] int, nondet : [int] bool) returns (out : [int] int);

