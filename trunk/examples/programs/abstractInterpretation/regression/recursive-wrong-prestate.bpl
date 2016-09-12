//#Safe
//
// Wrong (not inductive) transition and/or state added by AI
// The second disjunct of the hierachical pre state is probably the reason. 
// 
// PreState:			(and (= foo_bla 0) (= foo_res 0))
// HierachicalPreState 	(or (<= 1 foo_bla) (<= (+ foo_bla 1) 0))
// Trans: 				return;
// Post:				(and (= foo_res 0) (<= 1 foo_bla))
// 



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