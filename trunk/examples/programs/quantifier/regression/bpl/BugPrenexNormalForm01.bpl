//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-05-14
 * 
 * Triggered with backward predicates 
 */



var memA : [int]int;
var memB : [int]int;
var value : int;

procedure main() returns ();
modifies value;

implementation main() returns (){
    value := 23;
    while(*){}
    assume memB[0] == value;
    value := 42;
    while(*){}
    assume memA == memB[1 := value];
    assert memA[0] == 23;
}

