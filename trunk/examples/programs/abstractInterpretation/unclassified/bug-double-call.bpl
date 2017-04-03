//#Unsafe
// 2016-12-19 DD 
// Double-call with dual loop heads bug 
//
// Soundness check failed for the following triple (but also affects Octagons):
// Pre: {(= foo_e 0)}
// (= v_foo_local_1 v_foo_e_1) (local := e;)
// Post: {false}
// 

procedure foo(e : int) returns (){
    var local : int;

    local := e;
    while (true)
    {
        if (local >= 5) {
            break;
        }
        local := local + 1;
    }
}


procedure ULTIMATE.start() returns (){
    call foo(0);
    call foo(0);
    assert false;
}



