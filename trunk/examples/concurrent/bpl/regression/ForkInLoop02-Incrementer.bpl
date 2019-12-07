// #Unsafe
/*
 * We need two thread instances to find a counterexample.
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2019-11-20
 * 
 */

var n: int;

procedure ULTIMATE.start();
modifies n;

implementation ULTIMATE.start()
{
    var newid : int;
    newid := 0;
    n := 0;

    while (*) {
        fork newid foo();
        newid := newid + 1;
    }
}


procedure foo()
modifies n;
{
    n := n + 1;
    assert n <= 2;
}
