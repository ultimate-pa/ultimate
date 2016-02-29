//#Unsafe

procedure ULTIMATE.start()
{
        var x : int;

        assume x == 3;

        assert true;
        assert x != 3;
}
