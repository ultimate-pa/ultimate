implementation foo(#in~x : int) returns (#res : int)
{
    var ~x : int;

  $Ultimate##0:
    ~x := #in~x;
    #res := ~x + 3;
    return;
}

implementation bar() returns (#res : int)
{
  $Ultimate##0:
    #res := 4;
    return;
}

implementation main() returns (#res : int)
{
    var ~j~3 : int;
    var #t~ret0 : int;
    var #t~ret1 : int;

  $Ultimate##0:
    call #t~ret0 := foo(~j~3);
    ~j~3 := #t~ret0;
    havoc #t~ret0;
    call #t~ret1 := bar();
    ~j~3 := #t~ret1;
    havoc #t~ret1;
    return;
}

implementation ULTIMATE.init() returns ()
{
  $Ultimate##0:
    return;
}

implementation ULTIMATE.start() returns ()
{
    var #t~ret2 : int;

  $Ultimate##0:
    call ULTIMATE.init();
    call #t~ret2 := main();
    return;
}

procedure foo(#in~x : int) returns (#res : int);
    modifies ;

procedure bar() returns (#res : int);
    modifies ;

procedure main() returns (#res : int);
    modifies ;

procedure ULTIMATE.init() returns ();
    modifies ;
    modifies ;

procedure ULTIMATE.start() returns ();
    modifies ;
    modifies ;

