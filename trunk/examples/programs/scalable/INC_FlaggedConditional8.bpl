//#Safe
/*
 * Author: nutz@informatik.uni-freiburg.de
 *
 */

procedure foo(){
	var x:int;
	var y, z, a, x1, x2, x3, x4:int;
	var flag1, flag2, flag3 :bool;

	flag1:=true;
	flag2:=true;
	flag3:=true;
	
	if (*){
		flag1 := false;
	}
	if (*){
		flag2 := false;
	}
	if (*){
		flag3 := false;
	}
	


	x:=0;
	y:=0;
	z:=0;
	a:=0;
	x1:=0;
	x2:=0;
	x3:=0;
	x4:=0;
	
	while(*){
		if(flag1 == true) {
			if(flag2 == true) {
				if (flag3 == true){
					x:=x+1;
				} else {
					y:=y+1;
				}
			}
			else {
				if (flag3 == true){
					z:=z+1;
				} else {
					a:=a+1;
				}
			}
		}
		else {
			if(flag2 == true) {
				if (flag3 == true){
					x1:=x1+1;
				} else {
					x2:=x2+1;
				}
			}
			else {
				if (flag3 == true){
					x3:=x3+1;
				} else {
					x4:=x4+1;
				}
			}
		}
	}
	
	assert((x>=0 && y==0 && z==0 && a==0 && x1==0 && x2==0 && x3==0 && x4==0) || (x==0 && y>=0 && z==0 && a==0 && x1==0 && x2==0 && x3==0 && x4==0) || (x==0 && y==0 && z>=0 && a==0 && x1==0 && x2==0 && x3==0 && x4==0) 	|| (x==0 && y==0 && z==0 && a>=0 && x1==0 && x2==0 && x3==0 && x4==0) 	|| (x==0 && y==0 && z==0 && a==0 && x1>=0 && x2==0 && x3==0 && x4==0) 	|| (x==0 && y==0 && z==0 && a==0 && x1==0 && x2>=0 && x3==0 && x4==0) || (x==0 && y==0 && z==0 && a==0 && x1==0 && x2==0 && x3>=0 && x4==0) || (x==0 && y==0 && z==0 && a==0 && x1==0 && x2==0 && x3==0 && x4>=0));
}