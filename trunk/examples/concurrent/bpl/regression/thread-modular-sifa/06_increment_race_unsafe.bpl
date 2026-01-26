//#Unsafe

var counter: int;

procedure ULTIMATE.start()
modifies counter;
{
    counter := 0;
    fork 1 increment();
    fork 2 increment();
    join 1;
    join 2;
    assert counter == 2;  // UNSAFE: race condition, could be 1
}

procedure increment()
modifies counter;
{
    counter := counter + 1;
}
