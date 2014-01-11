//#Unsafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Simple program which is not correct.
 * In order to find a valid counterexample one has to unwind the loop several times
 *
 */

procedure incorrectEx()
{
  var i : int;

  i := 12;

  while (*) {
    i := i-1;
  } 
  
  assert(i>=0);

}

