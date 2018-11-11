/*
 * A little example to present the atomic statement.
 *
 * Author: Lars Nitzke (lars.nitzke@mailfence.com)
 * Date: 2018-11-11
 * 
 * We check if the atomic statement
 */

 var n: int;

 procedure ULTIMATE.start();
modifies n;

implementation ULTIMATE.start()
{
    var i: int;
    i := 0;
    n := 0;

    fork 1 foo();

    atomic {
        while (i < 10) {
            n := n + 1;
            i := i + 1;
        }
    }
    
    join 1;
}

procedure foo();
modifies n;

implementation foo()
{
    n := 1;
}