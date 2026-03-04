var n: int;
var done: bool;

procedure ULTIMATE.start()
modifies n;
modifies done;
{
    fork 1 foo();

    atomic {
        done := false;

        while (!done)
        {
          call inc();
          n := n + 1;
          done := true;
        }
    }

}

procedure foo()
modifies n;
{
    n := n * 2;
}

procedure inc();
modifies n;
ensures n == old(n)+1;
