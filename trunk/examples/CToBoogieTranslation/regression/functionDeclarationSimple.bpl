implementation foo(#in~x : int) returns (#res : int)
{
    var ~x : int;

  $Ultimate##0:
    ~x := #in~x;
    #res := 0;
    return;
}

implementation main() returns (#res : int)
{
  $Ultimate##0:
    ~i~1 := 1;
    return;
}

var ~i~1 : int;
implementation ULTIMATE.init() returns ()
{
  $Ultimate##0:
    ~i~1 := 0;
    return;
}

implementation ULTIMATE.start() returns ()
{
    var #t~ret0 : int;

  $Ultimate##0:
    call ULTIMATE.init();
    call #t~ret0 := main();
    return;
}

procedure foo(x : int) returns (#res : int);
    modifies ;

procedure main() returns (#res : int);
    modifies ~i~1;

procedure ULTIMATE.init() returns ();
    modifies ~i~1;
    modifies ;

procedure ULTIMATE.start() returns ();
    modifies ~i~1, ~i~1;
    modifies ~i~1;

