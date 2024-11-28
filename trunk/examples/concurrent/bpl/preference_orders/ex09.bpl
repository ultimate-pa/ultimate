//#Safe
/*
 * Author: Dominik Klumpp
 *
 * Idea: Two threads, where one increments x and the other decrements x.
 *       Depending on which thread takes the first step and receives thread ID 0 (in its local "id_" variable),
 *       thread1 either increments x by c for 2n iterations, or thread1 increments x by 2*c for n iterations.
 *
 * The optimal schedules would be (t1 t2)* if thread1 receives ID 0, and (t1 t2 t2)* if thread1 receives ID 1.
 * As the received ID is determined by the order of the assignments to the respective "id_" variables,
 * the optimal schedules overall can be written as id1 id2 (t1 t2)* + id2 id1 (t1 t2 t2)*.
 * Here id1, id2 represent the respective atomic blocks initializing these variables,
 * and t1, t2 represent an iteration of the respective while-loop.
 */
var n, x, c : int;
var id_ctr : int;

procedure ULTIMATE.start()
modifies x, id_ctr;
{
  assume x == 0;

  id_ctr := 0;
  fork 1 thread1();
  fork 2 thread2();
  join 1;
  join 2;

  assert x == 0;
}

procedure thread1()
modifies x, id_ctr;
{
  var i, id1, limit : int;

  atomic {
    id1 := id_ctr;
    id_ctr := id_ctr + 1;
  }

  limit := if id1 == 0 then 2*n else n;

  i := 0;
  while (i < limit) {
    x := x + (if id1 == 0 then c else 2*c);
    i := i + 1;
  }
}

procedure thread2()
modifies x, id_ctr;
{
  var j, id2 : int;

  atomic {
    id2 := id_ctr;
    id_ctr := id_ctr + 1;
  }

  j := 0;
  while (j < 2*n)
  {
    x := x - c;
    j := j + 1;
  }
}
