var x : int;

procedure dec()
modifies x;
{
  x := x - 1;
}


procedure ULTIMATE.start()
modifies x;
{
    x := 3;
    
    while (x > 0) {
        fork 0 dec();
        x := x - 1;
    }
    
    while (x < 3) {
        join 0;
        x := x + 1;
    }
  
    assert x == 3;
}
