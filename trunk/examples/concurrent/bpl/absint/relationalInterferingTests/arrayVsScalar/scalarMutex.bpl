var w       : bool;
var x       : int;
var race_x  : int;

procedure Writer()
  modifies w, race_x;
{
  atomic {
    assume !w;
    w := true;
  }
  race_x := 0;
  assert race_x == 0;
  atomic {
    w := false;
  }
}

procedure Reader()
  modifies w, race_x;
{
  atomic {
    assume !w;
    w := true;
  }
  race_x := 1;
  assert race_x == 1;
  atomic {
    w := false;
  }
}

procedure ULTIMATE.start()
  modifies w, race_x;
{
  w := false;
  fork 1 Writer();
  fork 2 Reader();
}

