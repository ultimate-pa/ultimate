//#Safe
// Author: hoenicke@informatik.uni-freiburg.de
// Date: 2020-03-16
//
// Test for the const-array directive that we pass to Ultimate via attributes.
//
// Our wiki says the following.
// If a function `func` has the attribute `{:const_array}`, the RCFGBuilder
// will replace all calls to that function with a built-in SMT function that
// creates constant array.  The function `func` must take one argument of
// some boogie type `T` and must return a Boogie array type `[...]T`.

function { :const_array }
   const~x(value : int) returns ([int]int);

function { :const_array }
   const~xy(value : { x :int, y: bv32}) returns ([bv64]{x:int, y: bv32});

function { :const_array }
   const~mem(value : int) returns ([{base:int, offset:bv64}]int);

procedure ULTIMATE.start()
{
    assert const~x(1)[2] == 1;
    assert const~xy({x: 0, y: 3bv32})[17bv64] == {x:0, y:3bv32};
    assert const~mem(1)[{ base:17, offset: 12bv64}] == 1;
}