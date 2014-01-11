//#Safe
/*
 * Author: nutz@informatik.uni-freiburg.de
 *
 */

procedure foo(){
	var x:int;
	var y, z, a:int;
	var flag1, flag2:bool;

	flag1:=true;
	flag2:=true;
	
	if (*){
		flag1 := false;
	}
	if (*){
		flag2 := false;
	}

	x:=0;
	y:=0;
	z:=0;
	a:=0;
	
	while(*){
		if(flag1 == true) {
			if (flag2 == true){
				x:=x+1;
			} else {
				y:=y+1;
			}
		}
		else {
			if (flag2 == true){
				z:=z+1;
			} else {
				a:=a+1;
			}
		}
	}
	
	assert((x>=0 && y==0 && z==0 && a==0) || (x==0 && y>=0 && z==0 && a==0) || (x==0 && y==0 && z>=0 && a==0) || (x==0 && y==0 && z==0 && a>=0));
}