/**
* 2 non-loop threads, 1 disabled, 1 enabled, trivial combined guard disjunction
*/

var x: int;

procedure ULTIMATE.start()
modifies x;
{
  x := 0;

  fork 1 t1();
  fork 2 t2();
  fork 3 t3();
  join 1;
  join 2;
  join 3;
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
	assume x >= 0;
	x := -2;
}

procedure t3()
{
	assume x <= 0;
}


