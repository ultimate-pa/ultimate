//#rNonTermination
/*
 * Date: 2016-09-10
 * Author: heizmann@informatik.uni-freiburg.de
 */

var mem : [int]int;

procedure main() returns ();
modifies mem;

implementation main() returns (){
    var y : int;
    var p,q : int;
    var a : [int]int;

    havoc p;
    assume a[p] == 0;
	havoc a;
    while (true)
    {
        y := mem[p];
        havoc mem;
		assume mem[p] == y - 1;
    }
}

