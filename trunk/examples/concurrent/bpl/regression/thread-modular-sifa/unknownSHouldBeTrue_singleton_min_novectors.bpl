var v    : int;
var mem  : int;
var race : int;

procedure T1()
  modifies v, race;
{
  atomic {
    havoc v;
    race := 0;
  }
}

procedure TX()
  modifies mem, race;
{
  atomic {
    assert race == 0;
    race := 1;
    mem  := 88;
    race := 0;
  }
}

procedure TY()
  modifies mem, race;
{
  atomic {
    assert race == 0;
    race := 1;
    mem  := 89;
    race := 0;
  }
}

procedure ULTIMATE.start()
  modifies v, mem, race;
{
  race := 0;
  fork 1 T1();
  fork 2 TX();
  fork 3 TY();
}

