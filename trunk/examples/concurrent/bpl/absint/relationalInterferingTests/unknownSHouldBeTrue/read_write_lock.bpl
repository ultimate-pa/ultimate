var r : int;
var w : bool;
var x : int;
var race_x :

procedure RW_ReadLock()
  modifies r, w;
{
  atomic {
    assume !w;
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
    assume r == 0 && !w;
    w := true;
  }
}

procedure RW_WriteUnlock()
  modifies w;
{
  atomic {
    w := false;
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
  w := false;
  fork 1 Writer();
  fork 2 Reader();
}

