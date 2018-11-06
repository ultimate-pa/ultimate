//Safe 
// Daniel Dietsch 2018-11-06
type rational = { n, d: int, v:real };

// correct usage of :expand_struct 
function { :expand_struct "n" } { :smtdefined "(+ n 0)" } { :expand_struct "d" } { :smtdefined "(+ d 0)" } { :expand_struct "v" } { :smtdefined "(/ (to_real n) (to_real d))" } foo(n:int, d:int) returns (out:rational);

// incorrect: will loose first :smtdefined 
// function  { :smtdefined "n" } { :expand_struct "n" } { :smtdefined "d" } { :smtdefined "(div n d)" } bar(n:int, d:int) returns (out:rational);

// correct: will copy all attributes to foo.n (all other functions dont get any attributes) 
// function  { :expand_struct "n" } { :smtdefined "n" } { :smtdefined "d" } { :smtdefined "(div n d)" } bar(n:int, d:int) returns (out:rational);

// correct: will copy all attributes to foo.d (all other functions dont get any attributes) 
// function  { :expand_struct "d" } { :smtdefined "n" } { :smtdefined "d" } { :smtdefined "(div n d)" } bar(n:int, d:int) returns (out:rational);

// incorrect: has struct return type but not :expand_struct attribute 
// function  { :smtdefined "n" } { :smtdefined "d" } { :smtdefined "(div n d)" } bar(n:int, d:int) returns (out:rational);

// incorrect: has no struct return type but :expand_struct attribute 
// function  { :expand_struct "d" } { :smtdefined "n" } { :smtdefined "d" } { :smtdefined "(div n d)" } bar(n:int, d:int) returns (out:real);

// correct: no expand_struct and no struct return type 
// function { :smtdefined "(div n d)" } bar(n:int, d:int) returns (out:real);

// incorrect: :expand_struct has non-existent field as argument 
//function  { :expand_struct "x" } { :smtdefined "n" } { :smtdefined "d" } { :smtdefined "(div n d)" } bar(n:int, d:int) returns (out:rational);

// incorrect: :expand_struct has wrong argument type 
//function  { :expand_struct 1 } { :smtdefined "n" } { :smtdefined "d" } { :smtdefined "(div n d)" } bar(n:int, d:int) returns (out:rational);

// incorrect: :expand_struct has wrong number of arguments (TODO: possible feature?)
// function  { :expand_struct "n", "d" } { :smtdefined "n" } { :smtdefined "d" } { :smtdefined "(div n d)" } bar(n:int, d:int) returns (out:rational);

// incorrect: :expand_struct for the same field occurs twice 
// function { :expand_struct "n" } { :smtdefined "n" } { :expand_struct "n" } { :smtdefined "d" } { :expand_struct "v" } { :smtdefined "(div n d)" } bar(n:int, d:int) returns (out:rational);

function {:builtin "bvadd"} bvadd(a : bv8, b : bv8) returns (out : bv8);

procedure main() returns ()
{
   var a : rational;
   var b : bv8; 
   
   a := foo(1,2);
   assert a!n == 1;
   assert a!d == 2;
   assert a!v == 0.5;
   
   
   b := 1bv8;
   b := bvadd(b,b);
   assert b == 2bv8;
}


