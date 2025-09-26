//#Safe

var stoppingFlag, stoppingEvent, stopped : bool;
var pendingIo : int;

procedure ULTIMATE.start()
free requires pendingIo == 1 && !stopped && !stoppingEvent && !stoppingFlag;
modifies stoppingEvent, pendingIo;
{
    // enter
    atomic {
        assume !stoppingFlag;
        pendingIo := pendingIo + 1;
    }

    // do work
    assert !stopped;

    // exit
    atomic {
        pendingIo := pendingIo - 1;
        if (pendingIo == 0) {
            stoppingEvent := true;
        }
    }
}

procedure server()
free requires !stopped;
modifies stoppingFlag, stoppingEvent, stopped, pendingIo;
{
    stoppingFlag := true;

    // close
    atomic {
        pendingIo := pendingIo - 1;
        if (pendingIo == 0) {
            stoppingEvent := true;
        }
    }

    assume stoppingEvent;
    stopped := true;
}
