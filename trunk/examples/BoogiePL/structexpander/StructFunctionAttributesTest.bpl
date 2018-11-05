//Safe 
type rational = { n, d: int, v:real };

function { :expand_struct "n" } { :smtdefined "n" } { :expand_struct "d" } { :smtdefined "d" } { :expand_struct "v" } { :smtdefined "(div n d)" } foo(n:int, d:int) returns (out:rational);

function  { :smtdefined "n" } { :expand_struct "n" } { :smtdefined "d" } { :smtdefined "(div n d)" } bar(n:int, d:int) returns (out:rational);

procedure main() returns ()
{
   var a : rational;

   a := foo(1,2);
   assert a!n == 1;
   assert a!d == 2;
   assert a!v == 0.5;
}


