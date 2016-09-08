//#nonterminating
/*
 * Date: 2016-09-06
 * Author: Matthias Heizmann
 * 
 */


implementation ULTIMATE.start() returns (){
    #valid[0] := 0;
    call main();
}

implementation bubblesort(q : int) returns (){
    while (true)
    {
    }
}

implementation main() returns (){
    var p : int;

    call p := #Ultimate.alloc();
    call bubblesort(p);
}


var #valid : [int]int;


procedure #Ultimate.alloc() returns (r : int);
ensures old(#valid)[r] == 0;
ensures #valid == old(#valid)[r := 1];
modifies #valid;


procedure bubblesort(q : int) returns ();
modifies ;

procedure main() returns ();
modifies #valid;

procedure ULTIMATE.start() returns ();
modifies #valid;

