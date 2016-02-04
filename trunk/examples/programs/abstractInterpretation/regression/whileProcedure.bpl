//#Safe
/*
 */

procedure ULTIMATE.start()
{
  var x : int;
  x := 0;
  
  while (x < 100) {
    call x := foo(x);
  }

  x := 0;
  while (x < 100) {
    call x := foo(x);
  }
  
  assert(x == 100);
}

procedure foo(k : int) returns (res:int)
{
	if(k > 50){
		res := k + 1;
	} else{
		res := k + 2;
	}
}