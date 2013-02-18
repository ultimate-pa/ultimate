procedure main() returns () {
var warn, mad, ret: bool;
var t, tn, pp: int;
havoc warn, mad, t, tn;
pp := 0;
call ret:= encT(warn, mad, t, tn, pp);
assert (ret != false);
}
//////////////////////////////////////////
procedure encT(warn: bool, mad: bool, t: int, tn:int, pp:int) returns (ret: bool){
	if (pp == 1) goto L1;
	if (pp == 2) goto L2;
	if (pp == 3) goto L3;
	if (pp == 4) goto L4;
	if (pp == 5) goto L5;
	if (pp == 6) goto L6;
	if (pp == 7) goto L7;
	if (pp == 8) goto L8;
	if (pp == 9) goto L9;
	while(true){
		havoc tn;
		label L1:
		if (*) {ret:= true; return;}
		call ret:= encTL(warn, mad, t, tn , 1);
		if (!ret){
			ret:= false; return;
		}
		t := tn - 10;
		label L2:
		if (*) {ret:= true; return;}
		call ret:= encTL(warn, mad, t, tn , 2);
		if (!ret){
			ret:= false; return;
		}
		if(t > 13){
			warn := true;
			label L4:
			if (*) {ret:= true; return;}
			call ret:= encTL(warn, mad, t, tn , 4);
			if (!ret){
				ret:= false; return;
			}
			mad := true;
			label L5:
			if (*) {ret:= true; return;}
			call ret:= encTL(warn, mad, t, tn , 5);
			if (!ret){
				ret:= false; return;
			}
		} else {
			warn := false;
			label L7:
			if (*) {ret:= true; return;}
			call ret:= encTL(warn, mad, t, tn , 7);
			if (!ret){
				ret:= false; return;
			}
		}
	}
}
//////////////////////////////////////////
procedure encTL(warn: bool, mad: bool, t: int, tn:int, pp:int) returns (ret: bool){
call ret:= encTLL(warn, mad, t, tn, pp);
if(ret){
return;
} else {
call ret:= encTLR(warn, mad, t, tn, pp);
return;
}
}
//////////////////////////////////////////
procedure encTLL(warn: bool, mad: bool, t: int, tn:int, pp:int) returns (ret: bool){
return !warn
}
//////////////////////////////////////////
procedure encTLR(warn: bool, mad: bool, t: int, tn:int, pp:int) returns (ret: bool){
if (pp == 0) goto L0;
if (pp == 1) goto L1;
if (pp == 2) goto L2;
if (pp == 3) goto L3;
if (pp == 4) goto L4;
if (pp == 5) goto L5;
if (pp == 6) goto L6;
if (pp == 7) goto L7;
if (pp == 8) goto L8;
if (pp == 9) goto L9;
while(true){
label L0:
if (*) {ret:= true; return;}
call ret:= encTLRL(warn, mad, t, tn , 0);
if (!ret){
call ret:= encTLRR(warn, mad, t, tn, 0);
return;
}
havoc tn;
label L1:
if (*) {ret:= true; return;}
call ret:= encTLRL(warn, mad, t, tn , 1);
if (!ret){
call ret:= encTLRR(warn, mad, t, tn, 1);
return;
}
t := tn - 10;
label L2:
if (*) {ret:= true; return;}
call ret:= encTLRL(warn, mad, t, tn , 2);
if (!ret){
call ret:= encTLRR(warn, mad, t, tn, 2);
return;
}
if(t > 13){
label L3:
if (*) {ret:= true; return;}
call ret:= encTLRL(warn, mad, t, tn , 3);
if (!ret){
call ret:= encTLRR(warn, mad, t, tn, 3);
return;
}
warn := true;
label L4:
if (*) {ret:= true; return;}
call ret:= encTLRL(warn, mad, t, tn , 4);
if (!ret){
call ret:= encTLRR(warn, mad, t, tn, 4);
return;
}
mad := true;
label L5:
if (*) {ret:= true; return;}
call ret:= encTLRL(warn, mad, t, tn , 5);
if (!ret){
call ret:= encTLRR(warn, mad, t, tn, 5);
return;
}
} else {
label L6:
if (*) {ret:= true; return;}
call ret:= encTLRL(warn, mad, t, tn , 6);
if (!ret){
call ret:= encTLRR(warn, mad, t, tn, 6);
return;
}
warn := false;
label L7:
if (*) {ret:= true; return;}
call ret:= encTLRL(warn, mad, t, tn , 7);
if (!ret){
call ret:= encTLRR(warn, mad, t, tn, 7);
return;
}
}
label L8:
if (*) {ret:= true; return;}
call ret:= encTLRL(warn, mad, t, tn , 8);
if (!ret){
call ret:= encTLRR(warn, mad, t, tn, 8);
return;
}
}
label L9:
if (*) {ret:= true; return;}
call ret:= encTLRL(warn, mad, t, tn , 9);
if (!ret){
call ret:= encTLRR(warn, mad, t, tn, 9);
return;
}
}
//////////////////////////////////////////
procedure encTLRL(warn: bool, mad: bool, t: int, tn:int, pp:int) returns (ret: bool){
return warn
}
//////////////////////////////////////////
procedure encTLRR(warn: bool, mad: bool, t: int, tn:int, pp:int) returns (ret: bool){
if(*){
call ret:= encTLRRL(warn, mad, t, tn, pp);
} else {
call ret:= encTLRRR(warn, mad, t, tn, pp);
}
}
//////////////////////////////////////////
procedure encTLRRL(warn: bool, mad: bool, t: int, tn:int, pp:int) returns (ret: bool){
return !warn
}
//////////////////////////////////////////
procedure encTLRRR(warn: bool, mad: bool, t: int, tn:int, pp:int) returns (ret: bool){
if (pp == 0) goto L0;
if (pp == 1) goto L1;
if (pp == 2) goto L2;
if (pp == 3) goto L3;
if (pp == 4) goto L4;
if (pp == 5) goto L5;
if (pp == 6) goto L6;
if (pp == 7) goto L7;
if (pp == 8) goto L8;
if (pp == 9) goto L9;
while(true){
label L0:
if (*) {ret:= true; return;}
call ret:= encTLRRRL(warn, mad, t, tn , 0);
if (!ret){
ret:= false; return;
}
havoc tn;
label L1:
if (*) {ret:= true; return;}
call ret:= encTLRRRL(warn, mad, t, tn , 1);
if (!ret){
ret:= false; return;
}
t := tn - 10;
label L2:
if (*) {ret:= true; return;}
call ret:= encTLRRRL(warn, mad, t, tn , 2);
if (!ret){
ret:= false; return;
}
if(t > 13){
label L3:
if (*) {ret:= true; return;}
call ret:= encTLRRRL(warn, mad, t, tn , 3);
if (!ret){
ret:= false; return;
}
warn := true;
label L4:
if (*) {ret:= true; return;}
call ret:= encTLRRRL(warn, mad, t, tn , 4);
if (!ret){
ret:= false; return;
}
mad := true;
label L5:
if (*) {ret:= true; return;}
call ret:= encTLRRRL(warn, mad, t, tn , 5);
if (!ret){
ret:= false; return;
}
} else {
label L6:
if (*) {ret:= true; return;}
call ret:= encTLRRRL(warn, mad, t, tn , 6);
if (!ret){
ret:= false; return;
}
warn := false;
label L7:
if (*) {ret:= true; return;}
call ret:= encTLRRRL(warn, mad, t, tn , 7);
if (!ret){
ret:= false; return;
}
}
label L8:
if (*) {ret:= true; return;}
call ret:= encTLRRRL(warn, mad, t, tn , 8);
if (!ret){
ret:= false; return;
}
}
label L9:
if (*) {ret:= true; return;}
call ret:= encTLRRRL(warn, mad, t, tn , 9);
if (!ret){
ret:= false; return;
}
}
//////////////////////////////////////////
procedure encTLRRRL(warn: bool, mad: bool, t: int, tn:int, pp:int) returns (ret: bool){
return mad
}
