
procedure bla ();

implementation bla () {

  var a, b : [int] int;

  var x,y : int;
  var i,j : int;
  var n : int;

  x := 0;
  j := 0;

  i := 0;

  assume n > 20;

  while (j < n) {
    j := j + 1;
    i := i + 1; //malloc(i)
    a[i] := x;
    b[i] := 3;
    x := i;
  }

  assert b[a[a[a[a[x]]]]] == 3;
}
