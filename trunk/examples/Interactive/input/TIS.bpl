//#Safe
//
// Trace Interpolant Selection example from proposal.
// should provide multiple interpolant sequences
// 



procedure ULTIMATE.start()
{
    var b : int;
    var i : int;
    i := 0;

    if (b > 0) {
        while (i < 100) {
            i := i +1;
        }
    }

    if (i != 0) {
        assert(b > 0);
    }
}