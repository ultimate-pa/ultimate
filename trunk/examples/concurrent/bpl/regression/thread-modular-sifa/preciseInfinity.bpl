var x : int;
var mutex : int;

procedure ULTIMATE.start()
modifies mutex, x;
{
    mutex := 0;
    x := 0;

    while (*) {
        fork 1 one();
    }
}

procedure one()
modifies mutex, x;
{
  atomic {
    assume mutex == 0;
    mutex := 1;
  }

    x := x + 1;
    assert x == 1;
    x := x - 1;

    mutex := 0;
}

