// #Safe

var y : int;

procedure inc() returns () 
modifies y;
{
	while (y < 2) {
		y := y + 1;
	}
}


procedure main() returns ()
modifies y;
{
    var x : int;
    x:=0;
    assume (y == x);
    call inc();
    assert (y == 2);
}
