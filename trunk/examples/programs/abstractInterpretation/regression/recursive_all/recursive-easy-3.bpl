//#Safe

procedure ULTIMATE.start()
{
  var z : int;
  call z := subToZero(20, 1);    
  assert(z == 0);       
}                       

procedure subToZero(a, b : int) returns (res : int)
{ 
	if(b<1){
		res := 0;
	} else if (a<0) {
		res := 0;
	} else{
		call res := subToZero(a-1, b);    	
	}
}