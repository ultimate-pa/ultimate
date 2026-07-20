/**
* program mit loop im nicht-loop thread um generalisierungsauswirkungen zu testen.//
*/

var x, y: int;

procedure ULTIMATE.start()
modifies x,y;
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
modifies x,y;
{	
	while (y>0){
	y:= y-1;
	y := y;
	}
	x := -2;
}


