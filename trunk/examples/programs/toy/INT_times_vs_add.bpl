//#Safe
//author: nutz@informatik.uni-freiburg.de

procedure TimesVsAdd()
{
    var x, y, x0, y0, result1, result2 : int;

    assume(x >= 0 && y >=0);

    x0 := x;
    y0 := y;
    result1 := 0;
    
    while (x > 0)
    {
        y := y0;
        while(y > 0) {
            result1 := result1 + 1;
            y := y - 1;
        }
        x := x - 1;
    }
    
    result2 := 0;
    x:= x0;
    y:= y0;

    while (y > 0) {
        result2 := result2 + x;
        y := y - 1;
    }

    assert(result1 == result2);

}
