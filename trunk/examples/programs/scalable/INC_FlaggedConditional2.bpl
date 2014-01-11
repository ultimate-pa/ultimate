//#Safe
/*
 * Author: nutz@informatik.uni-freiburg.de
 *
 */

procedure foo(){
	var x:int;
	var y:int;
	var flag:bool;

	flag:=true;
	
	if (*){
		flag := false;
	}

	x:=0;
	y:=0;
	
	while(*){
		if (flag == true){
			x:=x+1;
		} else {
			y:=y+1;
		}
	}
	
	assert(x==0 || y==0);
}