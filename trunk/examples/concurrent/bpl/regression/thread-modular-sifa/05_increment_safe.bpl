var counter: int;

procedure ULTIMATE.start()
modifies counter;
{
    counter := 0;
    fork 1 increment();
    
    counter := counter + 1;
    
    assert counter >= 1;
    assert counter <= 2;
}

procedure increment()
modifies counter;
{
    counter := counter + 1;
}
