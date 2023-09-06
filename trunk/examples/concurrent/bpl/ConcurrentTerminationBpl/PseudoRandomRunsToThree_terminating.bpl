var n, middle : int;

procedure ULTIMATE.start()
modifies  n, middle;
{
  n :=9;
  middle := 0;
  
  fork 1 one();
  fork 2 two();
  
  join 1;
  join 2;
}

procedure one()
modifies n, middle;
{
  while (middle == 2) {
    n := (n*n)%1000;
    middle := (n/ 10) % 10;
  }
}

procedure two()
modifies n, middle;
{
  while (middle != 3) {
    n := (n+n)%1000;
    middle := (n/ 10) % 10;
  }
}
