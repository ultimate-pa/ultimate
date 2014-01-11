//#Safe
//added by nutz@informatik.uni-freiburg.de
//would be scalable (if someone is interested..)
/*
 * Author: ermis@informatik.uni-freiburg.de
 */

procedure foo(){
	var x:int;
	var y:int;
	var flag:bool;

	flag:=true;

	x:=10;
	y:=0;
	while(*)
		invariant((x==0 && y==10 && flag==false) || (y==0 && x==10 && flag==true));
		{
		if (*){
			flag := false;
		} else {
			flag := true;
		}
		if (flag == true){
			while(y>0){
				x:=x+1;
				y:=y-1;
			}
		} else {
			while(x>0){
				y:=y+1;
				x:=x-1;
			}
		}
	}
	
	assert(x==0 || y==0);
}