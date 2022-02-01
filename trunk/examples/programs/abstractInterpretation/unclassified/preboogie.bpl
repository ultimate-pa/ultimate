procedure fibo(#in~n : int) returns (#res : int){
    var #t~ret0 : int;
    var #t~ret1 : int;
    var ~n : int;

    ~n := #in~n;
    if (~n == 0) {
    } else {
        call #t~ret0 := fibo(~n - 1);
        //assume -2147483648 <= #t~ret0 && #t~ret0 <= 2147483647;
        call #t~ret1 := fibo(~n - 1);
        //assume -2147483648 <= #t~ret1 && #t~ret1 <= 2147483647;
        #res := #t~ret0 + #t~ret1;
        havoc #t~ret0;
        havoc #t~ret1;
        return;
    }
}

procedure ULTIMATE.start() returns (){
    var #t~ret2 : int;
    var ~x~3 : int;

    ~x~3 := 3;
    call #t~ret2 := fibo(~x~3);
    //assume -2147483648 <= #t~ret2 && #t~ret2 <= 2147483647;
    havoc #t~ret2;
  ERROR:
    assert false;
}
