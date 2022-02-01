//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-12-04
 * 
 * Backward predicate lead to "nested self-upate" problem.
 * Workaround for problem by following commit.
 * https://github.com/ultimate-pa/ultimate/commit/9739c6611c5a55f9d32d3f7af7562f48fe5fb7ef
 */

implementation ULTIMATE.start() returns (){
    var #t~ret0 : int;

    call ULTIMATE.init();
    call #t~ret0 := main();
}

implementation main() returns (#res : int){
    var p : $Pointer$;

    call p := ~malloc(8);
    call ULTIMATE.dealloc(p);
}

var #valid : [int]bool;

procedure ULTIMATE.dealloc(~addr : $Pointer$) returns ();
free ensures #valid == old(#valid)[~addr!base := false];
modifies #valid;

procedure ~malloc(~size : int) returns (#res : $Pointer$);
ensures old(#valid)[#res!base] == false;
ensures #valid == old(#valid)[#res!base := true];
modifies #valid;

type $Pointer$ = { base : int, offset : int };
procedure main() returns (#res : int);
modifies #valid;
ensures #valid == old(#valid);

procedure ULTIMATE.init() returns ();

procedure ULTIMATE.start() returns ();
modifies #valid;

