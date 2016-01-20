//#Safe
/*
 * Testing the inequality comparison operator.
 */

procedure ULTIMATE.start()
{
  var x : real;
  assume(x >= 0.0);
  if (x != 0.0)
  {
    assert(x > 0.0);
  }
}
