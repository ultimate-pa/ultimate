//#Unsafe
/*
 * Example where in each iteration a different fact about the same variable
 * (here: x multiple of 2, x multiple of 3, x multiple of 4,) is important.
 * Trace Abstraction might be very efficient here.
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
  assume( x%5 == 0 );
  assume( x%7 == 0 );
  assume( x%11 == 0 );
  assume( x%13 == 0 );
  assume( x%17 == 0 );
  assume( x%19 == 0 );
  assume( x%23 == 0 );
  assume( x%31 == 0 );
  assume( x%41 == 0 );

  i:=0;
  while (i != 3)
  {
    i:=i+1;
    x:=x+x;
  }

  if( x%2 != 0 ){ goto ERROR; }
  if( x%3 != 0 ){ goto ERROR; }
  if( x%5 != 0 ){ goto ERROR; }
  if( x%7 != 0 ){ goto ERROR; }
  if( x%11 != 0 ){ goto ERROR; }
  if( x%13 != 0 ){ goto ERROR; }
  if( x%17 != 0 ){ goto ERROR; }
  if( x%19 != 0 ){ goto ERROR; }
  if( x%23 != 0 ){ goto ERROR; }
  if( x%31 != 0 ){ goto ERROR; }
  if( x%37 != 0 ){ goto ERROR; }
  if( x%41 != 0 ){ goto ERROR; }
  if( x%1111 != 0 ){ goto ERROR; }
  
  if (false) {
    ERROR:
    assert(false);
  }

}
