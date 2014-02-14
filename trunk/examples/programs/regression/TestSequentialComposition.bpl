//#Safe
/*
 * Date: 06.06.2011
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Several tests for the sequential composition of TransFormulas.
 * 
 * different cases:
 * 1. y does not occur: assume(true)
 * 2. y is only inVar: a := y;
 * 3. y is only outVar: y := a;
 * 4. y is inVar and outVar y := y + 1;
 */

procedure proc()
{
  var in, a, y: int;

  // case 1-1
  y,a := 0, 10;
  assume(true);
  assume(true);
  assert(y == 0);

  
  //case 1-2
  y,a := 0, 10;
  assume(true);
  a := y;
  assert (y == 0);

  
  //case 1-3
  y,a := 0, 10;
  assume(true);
  y := a;
  assert (y == 10);

  
  //case 1-4
  y,a := 0, 10;
  assume(true);
  y := y + 1;
  assert (y == 1);
  

  
  // case 2-1
  y,a := 0, 10;
  a := y;
  assume(true);
  assert(y == 0);

  
  //case 2-2
  y,a := 0, 10;
  a := y;
  a := y;
  assert (y == 0);

  
  //case 2-3
  y,a := 0, 10;
  a := y;
  y := a;
  assert (y == 0);

  
  //case 2-4
  y,a := 0, 10;
  a := y;
  y := y + 1;
  assert (y == 1);
    

  
  // case 3-1
  y,a := 0, 10;
  y := a;
  assume(true);
  assert(y == 10);

  
  //case 3-2
  y,a := 0, 10;
  y := a;
  a := y;
  assert (y == 10);

  
  //case 3-3
  y,a := 0, 10;
  y := a;
  y := a;
  assert (y == 10);

  
  //case 3-4
  y,a := 0, 10;
  y := a;
  y := y + 1;
  assert (y == 11);
      

  
  // case 4-1
  y,a := 0, 10;
  y := y + 1;
  assume(true);
  assert(y == 1);

  
  //case 4-2
  y,a := 0, 10;
  y := y + 1;
  a := y;
  assert (y == 1);

  
  //case 4-3
  y,a := 0, 10;
  y := y + 1;
  y := a;
  assert (y == 10);

  
  //case 4-4
  y,a := 0, 10;
  y := y + 1;
  y := y + 1;
  assert (y == 2);

}
