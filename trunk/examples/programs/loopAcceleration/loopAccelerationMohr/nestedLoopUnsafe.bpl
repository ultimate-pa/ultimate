//#Unsafe

procedure main() returns (#res : int){
    var x,y : int;

    x := 0;
    y := 0;
    while (x<100)
    {
        y := 0;
        while (y<10)
        {
            y:=y+1;
        }
        x:=x+1;
    }
    assert false;
}
