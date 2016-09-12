//#Safe

procedure ULTIMATE.start()
{
  var input : int;
  var result : int;
  
  call result := foo(input);    
  assert(result != 3);       
} 

procedure foo(a : int) returns (res : int)
{ 
	//without this additional variable, everything works out 
	var bla : int;
	bla := a;

	if(bla == 0){
		res := 0;
		return;
	}else{
		call res := foo(bla - 1);
		res := res +1;
		if(res > 2){
			res := 2;
		}
	}
}