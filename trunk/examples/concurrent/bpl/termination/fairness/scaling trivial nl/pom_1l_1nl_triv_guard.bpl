/**
* 
* terminates under fairness
*/

var x: int;

procedure ULTIMATE.start()
modifies x;
{
  x := 0;

  fork 1 t1();
  fork 2 t2();
  join 1;
  join 2;
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
	x := -2;
}




