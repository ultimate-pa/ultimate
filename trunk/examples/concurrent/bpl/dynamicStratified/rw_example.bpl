//#Safe
/*
 * Author: Dominik Klumpp
 * Date: June 2022
 */

var lock : int;
var A : [int]int;

function {:smtdefined "((as const (Array Int Int)) 0))"} zero() returns (L : [int]int);

procedure ULTIMATE.start()
modifies lock, A;
{
  A := zero();

  fork 1       writer();
  fork 2,2     readerWithAssert(2);
  fork 3,3,3   reader(2);
  fork 4,4,4,4 reader(2);
}

procedure readerWithAssert(step : int)
modifies lock;
{
  var x, y : int;
  var i : int;

  i := 0;

  while (true) {
    call acquire_read();
    x := A[i];
    y := A[i];
    call release_read();

    assert x == y;
    i := i + step;
  }
}

procedure reader(step : int)
modifies lock;
{
  var x, y : int;
  var i : int;

  i := 0;

  while (true) {
    call acquire_read();
    x := A[i];
    y := A[i];
    call release_read();

    i := i + step;
  }
}

procedure writer()
modifies lock, A;
{
  call acquire_write();
  A[0] := 3;
  call release_write();
}

procedure acquire_read()
modifies lock;
{
  atomic { assume lock >= 0; lock := lock + 1; }
}

procedure release_read()
modifies lock;
{
  lock := lock - 1;
}

procedure acquire_write()
modifies lock;
{
  atomic { assume lock == 0; lock := lock - 1; }
}

procedure release_write()
modifies lock;
{
  lock := lock + 1;
}
