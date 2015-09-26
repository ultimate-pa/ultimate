//#Safe
/*
 * 
 * In the loop there are always several different ways to increment x and y
 *
 * Date: 31.03.2014
 * Author: haettigj@informatik.uni-freiburg.de and heizmann@informatik.uni-freiburg.de 
 *
 */

procedure foo() {
	var x,y,f,g,q:int;
	x:=0;
	y:=0;
	q:=42;
	
	while(*)
	{
    if(g==0)
    {
      if(f==0)
      {
        x := x + 1;
        while (*) { q:=q+1;}
        x := x - 1;
      } else {
        y := y + 1;
        while (*) { q:=q+1;}
        y := y - 1;
      }	
    }else{
      if(f==0)
      {
        x := x + 2;
        while (*) { q:=q+1;}
        x := x - 2;
      } else {
        y := y + 2;
        while (*) { q:=q+1;}
        y := y - 2;
      }	
		}
	}
	assert(x == 0 && y == 0);
}
