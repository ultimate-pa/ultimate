//#Safe
// Worker has two phases; after join both must have completed.

var phase: int;

procedure ULTIMATE.start()
modifies phase;
{
    phase := 0;
    fork 1 worker();
    join 1;
    assert phase >= 1;
}

procedure worker()
modifies phase;
{
    phase := 1;
    phase := 2;
}
