/**
* 2 non-loop threads, 1 disabled, 1 enabled, trivial guard disjunction
* nonterminating
*/

var x: int;

procedure ULTIMATE.start()
modifies x;
{
  x := 0;

  fork 1 t1();
  fork 2 t2();
  fork 3 t2();
  fork 4 t2();
  join 1;
  join 2;
  join 3;
  join 4;
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
	assume false;
	x := -2;
}


