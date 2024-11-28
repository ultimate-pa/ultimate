//#Safe
/*
 * Author: Emma Bach
 *
 * Idea: Variant of ex11.bpl with different if/else conditions that might end up making the order more complex?
 *
 * The optimal schedules would still be (t_1 t_2) whenever t_1 is in the outer "if", (t_1 t_2 t_2) 
 * whenever it is in the inner "if", and (t_1 t_2 t_2 t_2) whenever it is in the innter "else".
 */
var n, x, c: int;

procedure ULTIMATE.start()
modifies x;
{
  assume x == 0;

  fork 1 thread1();
  fork 2 thread2();
  join 1;
  join 2;

  assert x == 0;
}

procedure thread1()
modifies x;
{
  var i : int;
  i := 0;

  while (i < 3 * n)
  {
    if (i % 3 == 0)
    {
      x := x + c;
    }
    else
    {
      if (i % 3 == 1)
      {
        x := x + 2 * c;
      }
      else
      {
        x := x + 3 * c;
      }
    }
    i := i + 1;
  }
}

procedure thread2()
modifies x;
{
  var j : int;
  j := 0;

  while (j < 6 * n)
  {
    x := x - c;
    j := j + 1;
  }
}
