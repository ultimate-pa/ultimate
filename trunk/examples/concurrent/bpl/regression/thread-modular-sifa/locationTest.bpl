//#Safe
var x, y: int;

procedure ULTIMATE.start()
modifies x, y;
{
    assume x == 0 || x == 2;
    fork 1 Thread1();
}

procedure Thread1()
modifies x, y;
{  
    x := 1;
}
