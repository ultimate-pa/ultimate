//#Safe
/* 
 */

procedure ULTIMATE.start()
{
  var x : int;
  x := 0;
  while(x<10){
	call x := inc(x);
  }
  
  assert(x == 10);
}

procedure inc(i : int) returns (res : int)
{ 
	res := i + 1;
}
