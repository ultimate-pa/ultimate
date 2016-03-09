//#Safe
/*
 *
 */
procedure main()
{
  var x,y: int;
  x := 0;
  y := 1000000;

  while(*){
    x := x+1;
	if(x==y){
	  break;
	}
  }
  assert(x <= y);
}