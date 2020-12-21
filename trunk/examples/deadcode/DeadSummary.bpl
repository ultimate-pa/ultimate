//#Safe
/*
    Call to procedure proc is dead. Triggered a bug (NullPointerException) in CfgBuilder.

    2020-12-02 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
*/

procedure ULTIMATE.start()
{
  var a, b : int;

  if (a > 0) {
    b := 1;
    goto my_label;
  } else {
    b := 0;
    goto my_label;
  }

  dead:
  call b := proc(a);
  assert b != 0;
  goto dead;

  my_label:
  return;
}

procedure proc(x : int) returns (y : int)
requires x >= 0;
{
  y := 1 - x;
}
