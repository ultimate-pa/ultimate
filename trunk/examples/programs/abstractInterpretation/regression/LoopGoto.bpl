//#Safe
/*
 *
 */
procedure main()
{
  var x,y: int;
  x := 0;
  y := 1000000;

BeforeLoop:  
  assume x<y;
  x := x + 1;
  goto AfterLoop,BeforeLoop;

AfterLoop:
  assume x>=y;
  assert(x == y);
}