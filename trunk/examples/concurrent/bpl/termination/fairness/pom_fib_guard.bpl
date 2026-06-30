/*
* non-loop ts should be enabled infinitely often.
* terminates under fairness, but we most likely won't be able to prove it.
*/

var x, f3: int;

procedure ULTIMATE.start()
modifies x, i;
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
	var f1, f2, f3, temp: int;
	f1 := 0;
	f2 := 1;
	f3 := 1;
	while (x >= 0){
	x := x + 1;
	if(x == f3){
		temp := f3;
		f3 := f2 + f1;
		f1 := f2;
		f2 := temp;
		
	}
	}
}

procedure t2()
modifies x;
{
	assume x == f3;
	x := x-2;
}