//#Safe

var s, t : int;
var crit : bool;

procedure ULTIMATE.start()
free requires s <= t && !crit;
modifies s, t, crit;
{
    var m : int;

    // request
    atomic {
        m := t;
        t := t + 1;
    }

    // failure
    assert m > s || !crit;

    // enter
    atomic {
        assume m <= s;
        crit := true;
    }

    // leave
    atomic {
        s := s + 1;
        crit := false;
    }
}
