var r : int;
var w : int;
var x : int;
var race_x :

procedure RW_ReadLock()
  modifies r, w;
{
  atomic {
    assume w == 0;
    r := r + 1;
  }
}

procedure RW_ReadUnlock()
  modifies r;
{
  atomic {
    r := r - 1;
  }
}

procedure RW_WriteLock()
  modifies r, w;
{
  atomic {
    assume r == 0 && w == 0;
    w := 1;
  }
}

procedure RW_WriteUnlock()
  modifies w;
{
  atomic {
    w := 0;
  }
}

procedure Writer()
  modifies x, r, w, race_x;
{
  var tmp : int;
  call RW_WriteLock();

  havoc tmp;
  race_x := tmp;
  assert race_x == tmp;
  x := 3;

  call RW_WriteUnlock();
}

procedure Reader()
  modifies r, w, race_x;
{
  var l, lx, ly : int;

  call RW_ReadLock();

  lx := x;
  ly := x;
  assert lx == ly;

  call RW_ReadUnlock();
}

procedure ULTIMATE.start()
  modifies x, r, w, race_x;
{
  r := 0;
  w := 0;
  fork 1 Writer();
  fork 2 Reader();
}

