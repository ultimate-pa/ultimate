var x : int;

procedure ULTIMATE.start()
modifies x;
{
  // {true}

  assume x == 0;

  // {x == 0}

  fork 1 thread1();
  fork 2 thread2();
    ...
  fork n threadn();
  join 1;
  join 2;
    ...
  join n;

  // {x == 0}

  assert x == 0;

  //
}

procedure thread1()
modifies x;
{
  ...
}

procedure thread2()
modifies x;
{
  // T2.1: {x == 0 || x == 1}

  x := x - 1;

  // T2.2: {x == -1 || x == 0}
}




// Non-Interference for T1.1 and thread2:
// { (x == 0 || x == -1) && (x == 0 || x == 1) }
// { x == 0 }
// x := x - 1;
// { x == 0 || x == -1 }


// Non-Interference for T1.2 and thread2: FAILS
// { (x == 1 || x == 0) && (x == 0 || x == 1) }
// { x == 0 || x == 1 }
// x := x - 1;
// { x == 0 || x == 1 }
