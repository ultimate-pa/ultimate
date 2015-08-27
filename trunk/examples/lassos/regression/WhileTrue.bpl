//#rNonTermination
/*
 * Date: 2012-03-19
 *
 */

procedure WhileTrue() returns (y: int)
{
  assume true;
  while (true) {
    y := 1;
  }
}

