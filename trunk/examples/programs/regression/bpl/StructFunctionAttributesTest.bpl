//#Safe 
// Daniel Dietsch 2018-11-06
type rational = { n, d: int, v:real };

function { :expand_struct "n" } { :smtdefined "(+ n 0)" } { :expand_struct "d" } { :smtdefined "(+ d 0)" } { :expand_struct "v" } { :smtdefined "(/ (to_real n) (to_real d))" } foo(n:int, d:int) returns (out:rational);

procedure main() returns ()
{
   var a : rational;
   
   a := foo(1,2);
   assert a!n == 1;
   assert a!d == 2;
   assert a!v == 0.5;
}


