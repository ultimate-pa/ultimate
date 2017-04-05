//#Unsafe
/*
 * AssertionError: No BoogieVar found
 * Bug in NonrelationalPostOperator.handleReturnTransition
 * Minimal example 
 */


const #funAddr~thread1 : $Pointer$;
axiom #funAddr~thread1 == { base: -1, offset: 0 };
const #funAddr~main_thread : $Pointer$;
axiom #funAddr~main_thread == { base: -1, offset: 1 };
var ~__CS_thread : [int]$Pointer$;

type $Pointer$ = { base : int, offset : int };


procedure ULTIMATE.start() returns ()
modifies ~__CS_thread;
{
    var #t~ret1 : $Pointer$;
	~__CS_thread[0] := { base: 0, offset: 0 };

    call #t~ret1 := ##fun~int~TO~$Pointer$(0, ~__CS_thread[0]);
    havoc #t~ret1;
    assert false;
}

procedure ##fun~int~TO~$Pointer$(#in~#param0 : int, #in~#fp : $Pointer$) returns (#res : $Pointer$){
    var #~#param0 : int;
    var #t~ret2 : $Pointer$;

    #~#param0 := #in~#param0;
    call #t~ret2 := main_thread(#~#param0);
    #res := #t~ret2;
    havoc #t~ret2;
    return;
}

procedure __CS_cs() returns (){
    var #t~ite0 : int;

    if (false) {
        #t~ite0 := 0;
    } else {
        #t~ite0 := 0;
    }
    havoc #t~ite0;
}

procedure __CS_pthread_create(#in~id1 : int, #in~attr : int, #in~t1 : $Pointer$, #in~arg : int) returns (){

}

procedure main_thread(#in~arg : int) returns (#res : $Pointer$){
    var ~arg : int;

    ~arg := #in~arg;
    call __CS_cs();
    call __CS_pthread_create(0, 0, #funAddr~thread1, 0);
    call __CS_cs();
}

