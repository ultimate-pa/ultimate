//#Safe
/*
 * Date: 25.7.2011
 * Author: Jan
 *
 *
 */

procedure HavocInLoop()
{
  var x, y : int;
  
  x := 0;
  y := 0;
	
  while (true) 
  {
    if (y < 0)     
    {
		y := -y;
    }
    else if (x < 0)     
    {
		x := -x;
    }
    
    if (*) 
    {
		havoc x;
    }
    else
    {
		havoc y;     
	}
	
    assert x >= 0 || y >= 0;
  }
}

