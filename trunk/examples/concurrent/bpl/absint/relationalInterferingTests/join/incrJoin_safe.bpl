// #Safe

var x : int; 
 
procedure ULTIMATE.start()
modifies x;
{
    var y1, y2 : int;
    var lastx : int;
    y1 := 3;
    y1 := y1 + 3;

    y2 := 10;

    x := 1;

    fork y1 one();
    fork y2, 0, 0 one();

    join 6;
    join 10, 0, 0;
    lastx := x;
    assert x == lastx;
}

procedure one()
modifies x;
{
    x := x + 1;
}

