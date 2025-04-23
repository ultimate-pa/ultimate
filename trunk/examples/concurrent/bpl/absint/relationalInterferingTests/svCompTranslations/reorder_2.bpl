// #Safe

var a: int;
var b: int;

procedure setter() modifies a, b;
{
  atomic {
    a := 1;
  }
  atomic {
    b := -1;
  }
}

procedure checker() modifies a, b;
{
  var la: int;
  var lb: int;

  atomic {
    la := a;
  }

  atomic {
    lb := b;
  }

  if (!((la == 0 && lb == 0) || (la == 1 && lb == -1))) {
    assert false;
  }
}

procedure ULTIMATE.start() modifies a, b;
{
  a := 0;
  b := 0;
  fork 1 setter();
  fork 2 checker();
}

