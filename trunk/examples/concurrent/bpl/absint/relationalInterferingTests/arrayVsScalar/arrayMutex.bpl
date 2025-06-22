var lock    : [int]int;
var idx     : int;
var race_x  : int;

procedure Writer()
  modifies lock, race_x;
{
  atomic {
    assume lock[idx] == 0;
    lock[idx] := 1;
  }
  race_x := 0;
  assert race_x == 0;
  atomic {
    lock[idx] := 0;
  }
}

procedure Reader()
  modifies lock, race_x;
{
  atomic {
    assume lock[idx] == 0;
    lock[idx] := 1;
  }
  race_x := 1;
  assert race_x == 1;
  atomic {
    lock[idx] := 0;
  }
}

procedure ULTIMATE.start()
  modifies lock, idx, race_x;
{
  havoc idx;
  lock[idx] := 0;
  fork 1 Writer();
  fork 2 Reader();
}

