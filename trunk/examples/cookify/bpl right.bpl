
var x:int;
var y:bool;

procedure main() returns () {
var warn, mad, ret: bool;
var t, tn, pp: int;
havoc warn, mad, t, tn;
pp := 0;
call ret:= encT(warn, mad, t, tn, pp);
assert (ret != false);
}
//////////////////////////////////////////
procedure encT(awarn: bool, amad: bool, at: int, atn:int, pp:int) returns (ret: bool)
{
	var warn, mad: bool;
	var t, tn: int;
	warn := awarn;
	mad := amad;
	t := at;
	tn := atn;
	if (pp == 4) {goto L3;}
	if (pp == 5) {goto L4;}
	if (pp == 7) {goto L7;}
	head:
	havoc tn;
	t := tn - 10;
	goto if1then, if1else;
      	if1then:
      	assume t> 13;
			warn := true;
			L3:
			if (*) {ret:= true; return;}
			call ret:= encTL(warn, mad, t, tn , 3);
			if (!ret){
				ret:= false; return;
			}
			mad := true;
			L4:
			if (*) {ret:= true; return;}
			call ret:= encTL(warn, mad, t, tn , 4);
			if (!ret){
				ret:= false; return;
			}
      	goto if1done;
      	if1else:
      	assume t <= 13;
			warn := false;
			L7:
			if (*) {ret:= true; return;}
			call ret:= encTL(warn, mad, t, tn , 7);
			if (!ret){
				ret:= false; return;
			}
      	goto if1done;
			if1done:
	goto head;
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
	ret := !warn;
	return;
}
//////////////////////////////////////////
procedure encTLR(awarn: bool, amad: bool, at: int, atn:int, pp:int) returns (ret: bool){
	var warn, mad: bool;
	var t, tn: int;
	warn := awarn;
	mad := amad;
	t := at;
	tn := atn;
	if (pp == 3) {goto L3;}
	if (pp == 4) {goto L4;}
	if (pp == 7) {goto L7;}
	head:
	havoc tn;
	t := tn - 10;
	goto if1then, if1else;
	if1then:
	assume t > 13;
		warn := true;
		L3:
		if (*) {ret:= true; return;}
		call ret:= encTLRL(warn, mad, t, tn , 3);
		if (!ret){
			call ret:= encTLRR(warn, mad, t, tn, 3);
			return;
		}
		mad := true;
		L4:
		if (*) {ret:= true; return;}
		call ret:= encTLRL(warn, mad, t, tn , 4);
		if (!ret){
			call ret:= encTLRR(warn, mad, t, tn, 4);
			return;
		}
	goto if1done;
	if1else:
	assume t <= 13;
		warn := false;
		L7:
		if (*) {ret:= true; return;}
		call ret:= encTLRL(warn, mad, t, tn , 7);
		if (!ret){
			call ret:= encTLRR(warn, mad, t, tn, 7);
			return;
		}
	goto if1done;
	if1done:
	goto head;
	}
//////////////////////////////////////////
procedure encTLRL(warn: bool, mad: bool, t: int, tn:int, pp:int) returns (ret: bool){
	ret:= warn;
	return;
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
	ret:= !warn;
	return;
}
//////////////////////////////////////////
procedure encTLRRR(awarn: bool, amad: bool, at: int, atn:int, pp:int) returns (ret: bool){
	var warn, mad: bool;
	var t, tn: int;
	warn := awarn;
	mad := amad;
	t := at;
	tn := atn;
	if (pp == 3) {goto L3;}
	if (pp == 4) {goto L4;}
	if (pp == 7) {goto L7;}
	head:
	havoc tn;
	t := tn - 10;
	goto if1then, if1else;
	if1then:
	assume t > 13;
		warn := true;
		L3:
		if (*) {ret:= true; return;}
		call ret:= encTLRRRL(warn, mad, t, tn , 3);
		if (!ret){
			ret:= false; return;
		}
		mad := true;
		L4:
		if (*) {ret:= true; return;}
		call ret:= encTLRRRL(warn, mad, t, tn , 4);
		if (!ret){
			ret:= false; return;
		}
	goto if1done;
	if1else:
	assume t <= 13;
		warn := false;
		L7:
		if (*) {ret:= true; return;}
		call ret:= encTLRRRL(warn, mad, t, tn , 7);
		if (!ret){
			ret:= false; return;
		}
	if1done:
	goto head;
	}
//////////////////////////////////////////
procedure encTLRRRL(warn: bool, mad: bool, t: int, tn:int, pp:int) returns (ret: bool){
	ret := mad;
	return;
}
