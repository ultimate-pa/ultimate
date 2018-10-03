//#Safe
/*
 * This example shows how fork and join works for different types as expression.
 * Only the thread that executes foo is joined because for the other
 * the return type does not match.
 *
 * Author: Lars Nitzke (lars.nitzke@outlook.com)
 * Date: 24.08.2018
 * 
 */

procedure ULTIMATE.start();

implementation ULTIMATE.start()
{
    var x : int;
    var y : bool;
    x := 1;
    y := true;

    fork 1 foo();
    fork 1 bar();
    fork 1 sam();
    
    join 1 assign x;
    assert x == 6;
}

procedure foo() returns (ret : int);

implementation foo() returns (ret : int)
{
    var x : int;
    x := 5;
    ret := x + 1;
}

procedure bar();

implementation bar() {
    var x : int;
    x := 5;
    x := x + 1;
}

procedure sam() returns (ret : bool);

implementation sam() returns (ret : bool) {
    ret := true;
}
