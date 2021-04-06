//#Unsafe
var x : bool;

procedure thread1()
modifies x;
{
    x := false;
    assume false;
}

procedure thread2()
{
    assert x;
}

procedure ULTIMATE.start()
modifies x;
{
    x := true;
    
    fork 1 thread1();
    fork 2 thread2();
}
