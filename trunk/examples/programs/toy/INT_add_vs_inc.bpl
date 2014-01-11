//#Safe
//author: nutz@informatik.uni-freiburg.de
/*
 * computes x + y by incrementing x y times. then checks it with the internal computation
 */


procedure add()
{
   var x, y, y0, result: int;

    assume(y >= 0);
    
    result := x;   
    y0 := y;
    
    while (y > 0)
    {
      result := result + 1;
      y := y - 1;
    }

    assert(result == (x + y0));
}
