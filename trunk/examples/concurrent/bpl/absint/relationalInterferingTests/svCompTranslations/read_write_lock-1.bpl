//#Safe

var x      : int;
var w      : bool;
var rcount : int;

procedure ULTIMATE.start()
  modifies w, rcount, x;
{
  w      := false;
  rcount := 0;

  fork 1 writer();
  fork 2 reader();
  fork 3 writer();
  fork 4 reader();
}

procedure writer()
  modifies w, rcount, x;
{
  atomic {
    assume !w && rcount == 0;
    w := true;
  }

  x := 3;

  w := false;
}

procedure reader()
  modifies w, rcount, x;
{
  var y : int;
  atomic {
    assume !w;
    rcount := rcount + 1;
  }

  y := x;
  assert y == x;

  atomic {
    rcount := rcount - 1;
  }
}

