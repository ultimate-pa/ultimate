var x : int;
var mutex : bool;

procedure ULTIMATE.start()
modifies mutex, x;
{
    mutex := false;
    x := 0;

    while (*) {
        fork 1 one();
    }
}

procedure one()
modifies mutex, x;
{
  atomic {
    assume !mutex;
    mutex := true;
  }

    x := 1;
    assert x == 1;
    x := 0;

    mutex := false;
}

