//#Safe
/*
 * Version of ManyFactsAboutX that might also show advantages of trace
 * abstraction if LBE is used.
 * Date: 24.06.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

var x, i: int;

procedure ManyFactsAboutX()
modifies i, x;
{


  assume( x%2 == 0 );
  assume( x%3 == 0 );
//   assume( x%5 == 0 );
//   assume( x%7 == 0 );
//   assume( x%11 == 0 );
//   assume( x%13 == 0 );
//   assume( x%17 == 0 );
//   assume( x%19 == 0 );
//   assume( x%23 == 0 );
//   assume( x%31 == 0 );
//   assume( x%37 == 0 );
//   assume( x%41 == 0 );

  i:=0;
  while (*)
  {
    i:=i+1;
    x:=x+x;
  }

  while (*) { if( x%2 != 0 ){ goto ERROR; } }
  while (*) { if( x%3 != 0 ){ goto ERROR; } }
//   while (*) { if( x%5 != 0 ){ goto ERROR; } }
//   while (*) { if( x%7 != 0 ){ goto ERROR; } }
//   while (*) { if( x%11 != 0 ){ goto ERROR; } }
//   while (*) { if( x%13 != 0 ){ goto ERROR; } }
//   while (*) { if( x%17 != 0 ){ goto ERROR; } }
//   while (*) { if( x%19 != 0 ){ goto ERROR; } }
//   while (*) { if( x%23 != 0 ){ goto ERROR; } }
//   while (*) { if( x%31 != 0 ){ goto ERROR; } }
//   while (*) { if( x%37 != 0 ){ goto ERROR; } }
//   while (*) { if( x%41 != 0 ){ goto ERROR; } }
  
  if (false) {
    ERROR:
    assert(false);
  }

}
