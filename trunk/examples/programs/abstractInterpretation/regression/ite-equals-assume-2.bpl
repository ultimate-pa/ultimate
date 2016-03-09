//#Unsafe

procedure ULTIMATE.start()
{
        var x : int;
        var b : bool;

        x := 5;
        assert true;

        assume b == (if x == 5 then 
        true else false);
        assert true;

        assert !b;
}
