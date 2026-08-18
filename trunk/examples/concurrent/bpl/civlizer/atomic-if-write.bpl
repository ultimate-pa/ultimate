var y : int;

procedure ULTIMATE.start()
{
  fork 1 thread();
  join 1;
}

procedure thread()
{
  var x : int;

  x := 0;

  assume y == 0;

  atomic {
    if (y != 0) {
      x := 7;
    }
  }

  assert x == 0;
  havoc x;
}
