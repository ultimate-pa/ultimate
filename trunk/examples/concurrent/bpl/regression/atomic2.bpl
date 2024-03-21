// #Safe
/*
 * Check that statements inside an atomic statement are executed
 * atomically (i.e., there must not be a context switch between
 * the execution of these statements.
 *
 * Author: Lars Nitzke (lars.nitzke@mailfence.com)
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 2024-02-20
 *
 */

var n: int;


procedure ULTIMATE.start()
modifies n;
{
    fork 1 foo();

    call __VERIFIER_atomic_begin();
        call inc();
        n := n + 1;
    call __VERIFIER_atomic_end();

}

procedure foo()
modifies n;
{
    n := n * 2;
}

procedure inc();
modifies n;
ensures n == old(n)+1;

procedure __VERIFIER_atomic_begin();
procedure __VERIFIER_atomic_end();
