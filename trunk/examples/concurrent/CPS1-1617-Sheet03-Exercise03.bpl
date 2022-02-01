//#cSafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-11-05
 */


var x: int;
var finished_processes: int;
 
 
procedure ~init() returns();
modifies x;
modifies finished_processes;

implementation ~init()
{
   x := 0;
   finished_processes := 0;
}


procedure Thread0() returns ();
modifies x;
modifies finished_processes;

implementation Thread0()
{
  var x_local, i: int;

  i := 1;
  while (i<=3) {
    x_local := x;
    x_local := x_local + 1;
    x := x_local;
    i := i + 1;
  }
  finished_processes := finished_processes + 1;
  assert (finished_processes == 3) ==> (x != 1);
}



procedure Thread1() returns ();
modifies x;
modifies finished_processes;

implementation Thread1()
{
  var x_local, i: int;

  i := 1;
  while (i<=3) {
    x_local := x;
    x_local := x_local + 1;
    x := x_local;
    i := i + 1;
  }
  finished_processes := finished_processes + 1;
}


procedure Thread2() returns ();
modifies x;
modifies finished_processes;

implementation Thread2()
{
  var x_local, i: int;

  i := 1;
  while (i<=3) {
    x_local := x;
    x_local := x_local + 1;
    x := x_local;
    i := i + 1;
  }
  finished_processes := finished_processes + 1;
}

