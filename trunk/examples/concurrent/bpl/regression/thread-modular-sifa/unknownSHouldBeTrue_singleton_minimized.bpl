var v    : int;
var mem  : [int]int;
var race : [int]int;

procedure T1()
  modifies v, race;
{
  atomic {
    havoc v;
    race[v] := 0;
  }
}

procedure TX()
  modifies mem, race;
{
  atomic {
    assert race[v] == 0;
    race[v] := 1;
    mem[v]  := 88;
    race[v] := 0;
  }
}

procedure TY()
  modifies mem, race;
{
  atomic {
    assert race[v] == 0;
    race[v] := 1;
    mem[v]  := 89;
    race[v] := 0;
  }
}

procedure ULTIMATE.start()
  modifies v, mem, race;
{
  fork 1 T1();
  fork 2 TX();
  fork 3 TY();
}

