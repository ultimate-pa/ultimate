//#Safe
/*
 * Author: ???
 * Note: The result of this test is not manually verified. DD just added the missing header based on some Ultimate results. 
 * 
 */

procedure while1() {
	var x:int;
	x:=0;
	while (x>0) {
		x:=x-1;
	}
	assert (x == 0);
}

procedure while2() {
	var x:int;
	x:=0;
	while (*) {
		x:=x-1;
	}
	assert (x <= 0);
}

procedure while3() {
	var x:int;
	x:=0;
	while (x>0) {
		x:=x-1;
	}
	x:=x+1;
	assert (x == 1);
}

procedure while4() {
	var x:int;
	x:=0;
	while (*) {
		x:=x-1;
	}
	x:=x+1;
	assert (x <= 1);
}

procedure if1() {
	var x:int;
	x:=0;
	if (x>0) {
		x:=x-1;
	}
	assert (x == 0);
}

procedure if2() {
	var x:int;
	x:=0;
	if (*) {
		x:=x-1;
	}
	assert (x == 0 || x == -1);
}

procedure if3() {
	var x:int;
	x:=0;
	if (x>0) {
		x:=x-1;
	} else {
		x:=x+1;
	}
	assert (x == 1);
}

procedure if4() {
	var x:int;
	x:=0;
	if (*) {
		x:=x-1;
	} else {
		x:=x+1;
	}
	assert (x != 0);
}