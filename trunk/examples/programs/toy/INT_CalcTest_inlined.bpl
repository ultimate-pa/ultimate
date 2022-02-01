//#Unsafe
//author: unknown
//added by nutz@informatik.uni-freiburg.de
//(I think it is unsafe by looking at it.., did not check thoroughly)

procedure main(){
	var result: int;
	var tmp: int;

	result := 0;
	tmp := 0;
	
	while(*)
	invariant(result != 10);{
		if (*){
			tmp := (tmp * 10);
		} else if (*){
			tmp := (tmp * 10) + 1;
		} else if (*){
			tmp := (tmp * 10) + 2;
		} else if (*){
			result := result + tmp;
			tmp := 0;
		}
	}
}