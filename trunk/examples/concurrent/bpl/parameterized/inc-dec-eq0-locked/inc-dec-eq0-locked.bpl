//#Safe

var x : int;
var lock : bool;

procedure thread()
free requires x == 0;
free ensures x == 0;
modifies x, lock;
{
  atomic { assume !lock; lock := true; }
  x := x + 1;
  x := x + 1;
  x := x + 1;
  x := x + 1;
  x := x - 1;
  x := x - 1;
  x := x - 1;
  x := x - 1;
  lock := false;
}

