/*
* non-loop ts should be enabled in every 4th iteration.
* terminates under fairness.
*/

var x, i: int;

procedure ULTIMATE.start()
modifies x, i;
{
  x := 0;
  i := 0;

  fork 1 t1();
  fork 2 t2();
  join 1;
  join 2;
}





procedure t1()
modifies x, i;
{
	while (x >= 0){
	x := x + 1;
	i := i + 1;
	if(i >= 4){
		i := i - 4;
	}
	}
}

procedure t2()
modifies x;
{
	assume i == 0;
	x := x-2;
}