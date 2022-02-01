// #Safe
/*
 * Check that statements inside an atomic statement are executed
 * atomically (i.e., there must not be a context switch between
 * the execution of these statements.
 *
 * Author: Lars Nitzke (lars.nitzke@mailfence.com)
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2018-11-11
 * 
 */

var n: int;


procedure ULTIMATE.start()
modifies n;
{
    fork 1 foo();

    atomic {
        call inc();
        n := n + 1;
    }

}

procedure foo()
modifies n;
{
    n := n * 2;
}

procedure inc();
modifies n;
ensures n == old(n)+1;
