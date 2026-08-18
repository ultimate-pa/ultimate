var x : int;

// var ghost : boolean;

procedure ULTIMATE.start()
modifies x;
{
  // {ghost == false}

  assume x == 0;

  // {x == 0 && ghost == false}

  fork 1 thread1();
  fork 2,2 thread2();
  join 1;
  join 2,2;

  // {x == 0 && ghost == true}

  assert x == 0;
}

procedure thread1()
modifies x;
{
  // T1.1: {(x == 0 || x == -1) && ghost == false}

  atomic {
    x := x + 1;
    // ghost := true;
  }

  // T1.2: {(x == 1 || x == 0) && ghost == true}
}

procedure thread2()
modifies x;
{
  // T2.1: {(x == 0 && ghost == false) || (x == 1 && ghost == true)}

  x := x - 1;

  // T2.2: {(x == -1 && ghost == false) || (x == 0 && ghost == true)}
}