//#Unsafe

var rwlock: int;
var x: int;
var y: int;

procedure thr1()
modifies rwlock, x;
{
    atomic {
        assume rwlock == 0;
        rwlock := -1;
    }

    x := 3;

    atomic {
        assume rwlock < 0;
        rwlock := 0;
    }
}

procedure thr2()
modifies rwlock, x, y;
{
    var l: int;
    var ly: int;
    var lx: int;

    atomic {
        assume rwlock >= 0;
        rwlock := rwlock + 1;
    }

    atomic { l := x; }
    atomic { y := l; }
    atomic { ly := y; }
    atomic { lx := x; }

    assert ly != lx;

    atomic {
        assume rwlock > 0;
        rwlock := rwlock - 1;
    }
}

procedure ULTIMATE.start()
modifies rwlock, x, y;
{
    rwlock := 0;
    x := 0;
    y := 0;

    fork 1 thr1();
    call thr2();
    join 1;
}
