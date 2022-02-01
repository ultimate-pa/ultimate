//#Terminating
/*
 * The disequality x != y would improve the map elimination.
 * However, whether x is an index of the array depends on the
 * the term that represents the relation of the stem.
 * 
 * If we rewrite equalities to a conjunction of two inequalities,
 * it is very unlikely that we obtain a term where x occurs as an
 * index of mem.
 * 
 * Date: 2018-07-29
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */

var mem : [int]int;

var x : int;
var y : int;
var w#ptr : int;
var r#ptr : int;


procedure ULTIMATE.start() returns ();
modifies mem, w#ptr, r#ptr;

implementation ULTIMATE.start() returns (){

    assume x > y;

    w#ptr := x;
    mem[w#ptr] := 1;
    
    while (true)
    {
        assume (mem[y] < 100);
        r#ptr := x;

        w#ptr := y;
        mem[w#ptr] := mem[y] + mem[r#ptr];
    }
}

