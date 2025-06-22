var max      : int;
var storage  : [int]int;

procedure ULTIMATE.start() returns ()
  modifies max, storage;
{
  var idx, tmp : int;

  max := -2147483648;

  idx := 0;
  while (idx < 6) {
    havoc tmp;
    storage[idx] := tmp;
    idx := idx + 1;
  }

  while (true) {
    fork 1 thr1();
  }
}

procedure thr1() returns ()
  modifies max;
{
  var offset, i, e : int;

  havoc offset;
  assume offset % 2 == 0
     && 0 <= offset
     && offset < 6;

  i := offset;

  while (i < offset + 2) {
    e := storage[i];

    atomic { if (e > max) { max := e; } }

    atomic { assert e <= max; }

    i := i + 1;
  }
}
