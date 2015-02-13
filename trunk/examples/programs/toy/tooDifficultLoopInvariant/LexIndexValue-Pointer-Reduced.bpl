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
  while (offset < 1048)
  {
    assert offset % 4 == 0;
    assert 4 + offset <= 1048;
    offset := offset + 4;
    assert offset % 4 == 0;
  }
}

procedure main() returns ();


