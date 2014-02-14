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

  var in, a, y: int;

procedure proc()
modifies y, a;
{

  // case 1-1
  y,a := 0, 10;
  if (*) {
    assume(true);
  } else {
    assume(true);
  }
  assert(y == 0 && a == 10);

  
  //case 1-2
  y,a := 0, 10;
  if (*) {
    assume(true);
  } else {
    a := y;
  }
  assert ((y == 0 && a == 10) || (y == 0 && a == 0));

  
  //case 1-3
  y,a := 0, 10;
  if (*) {
    assume(true);
  } else {
    y := a;
  }
  assert ((y == 0 && a == 10) || (y == 10 && a == 10));

  
  //case 1-4
  y,a := 0, 10;
  if (*) {
    assume(true);
  } else {
    y := y + 1;
  }
  assert ((y == 0 && a == 10) || (y == 1 && a == 10));

  
  
  //case 2-2
  y,a := 0, 10;
  if (*) {
    a := y;
  } else {
    a := y;
  }
  assert (y == 0 && a == 0);

  
  //case 2-3
  y,a := 0, 10;
  if (*) {
    a := y;
  } else {
    y := a;
  }
  assert ((y == 0 && a == 0) || (y == 10 && a == 10));

  
  //case 2-4
  y,a := 0, 10;
  if (*) {
    a := y;
  } else {
    y := y + 1;
  }
  assert ((y == 0 && a == 0) || (y == 1 && a == 10));
  
  
  //case 3-3
  y,a := 0, 10;
  if (*) {
    y := a;
  } else {
    y := a;
  }
  assert (y == 10 && a == 10);

  
  //case 3-4
  y,a := 0, 10;
  if (*) {
    y := a;
  } else {
    y := y + 1;
  }
  assert ((y == 10 && a == 10) || (y == 1 && a == 10));
      

  //case 4-4
  y,a := 0, 10;
  if (*) {
    y := y + 1;
  } else {
    y := y + 1;
  }
  assert ((y == 1 && a == 10));
  
  
  
  
   // additional example
   y,a := 0, 10;
   if (*) {
     y := y + 1;
   } else {
     a := a + 1;
   }
   assert ((y == 1 && a == 10) || (y == 0 && a == 11));
    
}