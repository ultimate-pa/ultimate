//#Nonterminating
/*
 * Date: 2016-08-31
 * Author: Matthias Heizmann
 * 
 * looked like a bug, but was just an wrong assert statement in the old
 * map elimination
 */

var mem : [int]int;


procedure main() returns (#res : int);
modifies mem;

implementation main() returns (#res : int){
    var x : int;
    var y : int;
    var ptr : int;
    var oldmem : [int]int;
    var some : int;

    ptr := x;
    assume mem == oldmem[x := 1];
    while (true)
    {
        ptr := y;
        havoc mem;
        assume mem == oldmem[y := some + some];
    }
}

