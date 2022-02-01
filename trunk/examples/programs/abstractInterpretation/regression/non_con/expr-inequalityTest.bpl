//#Safe
/*
 * Testing the inequality comparison operator.
 */

procedure ULTIMATE.start()
{
  var x : int;
  assume(x >= 0);
  if (x != 0)
  {
    assert(x > 0);
  }
}
