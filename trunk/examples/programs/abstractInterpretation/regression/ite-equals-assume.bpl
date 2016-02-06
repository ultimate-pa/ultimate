//#Unsafe

procedure ULTIMATE.start()
{
        var x : int;
        var b : bool;

        assume x >= 0 && x <= 10;
        assert true;

        assume b == (if x >= 5 then x == 8 else x == 2);
        assert true;

        assert !b;
}
