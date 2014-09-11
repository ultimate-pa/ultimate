//#Safe
/*
 * Reduced version of LexIndexValue-Pointer_true-termination.c
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2014-08-02
 */

implementation main() returns ()
{
  var offset, length: int;
  offset := 0;
  length := 1048;
  while (offset < length)
  {
    assert 4 + offset <= length;
    offset := offset + 4;
  }
}

procedure main() returns ();


