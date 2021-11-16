//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2021-11-15
 * 
 * Reveals bug in quantifier elimination for arrays.
 * After the bug is fixed, we can probably only keep the smallest of
 * the three examples.
 */
 
implementation ULTIMATE.start() returns (){


	#valid[0] := 0;
    call main();
}

implementation main() returns (){

    var p : $Pointer$;

    call p := #Ultimate.allocOnStack(12);
    call read~int({ base: p!base, offset: p!offset }, 4);
    call read~int({ base: p!base, offset: 4 + p!offset }, 4);
    call read~int({ base: p!base, offset: 8 + p!offset }, 4);
    call ULTIMATE.dealloc(p);
}


var #valid : [int]int;

type $Pointer$ = { base : int, offset : int };

procedure main() returns ();
modifies #valid;
ensures #valid == old(#valid);

procedure #Ultimate.allocOnStack(~size : int) returns (#res : $Pointer$);
ensures 0 == old(#valid)[#res!base];
ensures #valid == old(#valid)[#res!base := 1];
modifies #valid;


procedure read~int(#ptr : $Pointer$, #sizeOfReadType : int) returns ();
requires 1 == #valid[#ptr!base];
modifies ;

procedure ULTIMATE.dealloc(~addr : $Pointer$) returns ();
free ensures #valid == old(#valid)[~addr!base := 0];
modifies #valid;

procedure ULTIMATE.start() returns ();
modifies #valid;


