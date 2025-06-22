var blocked : bool;
var data : int;

procedure ULTIMATE.start() returns ()
  modifies data, blocked;
{
  blocked := false;
  data := 0;
  fork 1 thread1();
  fork 2 thread2();
  fork 3 thread3();
}

procedure thread1() returns ()
  modifies data, blocked;
{
  var temp : int;
  atomic { assume blocked == false; blocked := true;}
  atomic { data := data + 1; }
  temp := data;
  assert temp == data;
  atomic { blocked := false;}
}

procedure thread2() returns ()
  modifies data, blocked;
{
  var temp : int;
  atomic { assume blocked == false; blocked := true;}
  atomic { data := data + 2; }
  temp := data;
  assert temp == data;
  atomic { blocked := false;}
}

procedure thread3() returns ()
  modifies data, blocked;
{
  var temp : int;
  atomic { assume blocked == false; blocked := true;}
  atomic {
    if (data >= 4) {
      assert false;
    }
  temp := data;
  assert temp == data;
  }
  atomic { blocked := false;}
}

