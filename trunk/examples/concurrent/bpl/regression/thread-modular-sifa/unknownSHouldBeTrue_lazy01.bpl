var blocked : int;
var data : int;

procedure ULTIMATE.start() returns ()
  modifies data, blocked;
{
  blocked := 0;
  data := 0;
  fork 1 thread1();
  fork 2 thread2();
  fork 3 thread3();
}

procedure thread1() returns ()
  modifies data, blocked;
{
  var temp : int;
  atomic { assume blocked == 0; blocked := 1;}
  atomic { data := data + 1; }
  temp := data;
  assert temp == data;
  atomic { blocked := 0;}
}

procedure thread2() returns ()
  modifies data, blocked;
{
  var temp : int;
  atomic { assume blocked == 0; blocked := 1;}
  atomic { data := data + 2; }
  temp := data;
  assert temp == data;
  atomic { blocked := 0;}
}

procedure thread3() returns ()
  modifies data, blocked;
{
  var temp : int;
  atomic { assume blocked == 0; blocked := 1;}
  atomic {
    if (data >= 4) {
      assert 0 == 1;
    }
  temp := data;
  assert temp == data;
  }
  atomic { blocked := 0;}
}

