//#Safe
var w       : int;
var x       : int;
var race_x  : int;

procedure Writer()
  modifies w, race_x;
{
  atomic {
    assume w == 0;
    w := 1;
  }
  race_x := 0;
  assert race_x == 0;
  atomic {
    w := 0;
  }
}

procedure Reader()
  modifies w, race_x;
{
  atomic {
    assume w == 0;
    w := 1;
  }
  race_x := 1;
  assert race_x == 1;
  atomic {
    w := 0;
  }
}

procedure ULTIMATE.start()
  modifies w, race_x;
{
  w := 0;
  fork 1 Writer();
  fork 2 Reader();
}
