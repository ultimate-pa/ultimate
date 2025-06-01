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
    while (true) {
        if (!mutex) {
            mutex := true;
            break;
        }
    }

    x := 1;
    assert x == 1;
    x := 0;

    mutex := false;
}

