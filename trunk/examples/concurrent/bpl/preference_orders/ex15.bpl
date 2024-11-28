///#Safe
/*
 * Author: Emma Bach, Marcel Ebbinghaus
 *
 * Idea: Two threads, where one increments the value of x by c for n iterations and then by 2*c for another n iterations
 *       and the other decrements the value of x by c for 3n iterations.
 *
 * The optimal schedules would have a prefix of the form (t1 t2)^* followed, once thread1 exits its first loop, by (t1 t2)* when the second loop is in an "if" and (t1 t2 t2 t2) when it is in an "else"
 *       where t1, t2 stands for an iteration of the respective while-loop
 * 
 *
 * "i % 2 == 0" might be too simple of an if / else condition? Maybe if/else operator isnt needed since you can just alternate
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
  while (i < n)
  {
    x := x + c;
    i := i + 1;
  }

  i := 0;
  while (i < n)
  {
    if (i % 2 == 0)
    {
      x := x + c;
    }
    else
    {
      x := x + 3 * c;
    }
    i := i + 1;
  }
}

procedure thread2()
modifies x;
{
  var j : int;
  j := 0;

  while (j < 3 * n)
  {
    x := x - c;
    j := j + 1;
  }
}
