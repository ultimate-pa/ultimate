/**
* 1 non-loop thread, 3 loopthreads, trivial guard disjunction
* terminates
*/

var x: int;

procedure ULTIMATE.start()
modifies x;
{
  x := 0;

  fork 1 t1();
  fork 2 t1();
  fork 3 t1();
  fork 4 t1();
  fork 5 t2();
  join 1;
  join 2;
  join 3;
  join 4;
  join 5;
}





procedure t1()
modifies x;
{
	while (x >= 0){
	x := x + 1;
	}
}

procedure t2()
modifies x;
{
	x := -5;
}

