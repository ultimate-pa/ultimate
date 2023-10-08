var n, copyN, middle : int;

procedure ULTIMATE.start()
modifies  n, middle, copyN;
{
  n :=9;
  middle := 0;
  while (middle != 3){
  	copyN := n;
  	fork 1 one();
  	fork 2 two();
  	fork 3 three();
 
	join 1;
  	join 2;
  	join 3;
  	middle := n;
  	middle := middle % 10;
  }
}

procedure one()
modifies n;
{
  if (middle == 3) {
    n := (copyN*copyN) % 100;
    }
}

procedure two()
modifies n;
{
  n := (copyN+copyN) % 100;
}


procedure three()
modifies n;
{
  if (middle == 6) {
    n := (copyN*copyN) % 100;
  }
}

int mod(var x, y :int)
{
while(x > y){
x := x - y;
}
return x;
}