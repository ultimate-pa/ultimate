//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-06-15
 * 
 * Shows problem in computation of "future live" variables.
 * The oldvar of g is future live before the call of foo.
 * Our algorithm says that old(g) is not live.
 * 
 */


implementation ULTIMATE.start() returns (){
    var valueKeeper: bool;
    var retValue: bool;
    assume(valueKeeper == g);
    call retValue := list_add();
    assert(valueKeeper == retValue);
    return;
}

implementation foo() returns (){
    havoc g;
    return;
}

implementation list_add() returns (ret : bool){
    ret := g;
    call foo();
    return;
}

var g : bool;

procedure foo() returns ();
modifies g;

procedure list_add() returns (ret : bool);
modifies g;

procedure ULTIMATE.start() returns ();
modifies g;

