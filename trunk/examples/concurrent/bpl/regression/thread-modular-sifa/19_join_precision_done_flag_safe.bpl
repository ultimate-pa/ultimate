//#Safe
// After join, done must be 1.

var done: int;

procedure ULTIMATE.start()
modifies done;
{
    done := 0;
    fork 1 worker();
    join 1;
    assert done == 1;
}

procedure worker()
modifies done;
{
    done := 1;
}
