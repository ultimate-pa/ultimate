implementation main() returns (#res : int)
{
    var ~t~1.a : int;
    var ~s~1.a : int;
    var #t~ite0.a : int;

  $Ultimate##0:
    goto $Ultimate##1, $Ultimate##2;
  $Ultimate##1:
    assume true;
    #t~ite0.a := ~s~1.a;
    goto $Ultimate##3;
  $Ultimate##2:
    assume !true;
    #t~ite0.a := ~t~1.a;
    goto $Ultimate##3;
  $Ultimate##3:
    ~t~1.a := #t~ite0.a;
    havoc #t~ite0.a;
    return;
}

implementation ULTIMATE.init() returns ()
{
  $Ultimate##0:
    return;
}

implementation ULTIMATE.start() returns ()
{
    var #t~ret1 : int;

  $Ultimate##0:
    call ULTIMATE.init();
    call #t~ret1 := main();
    return;
}

procedure main() returns (#res : int);
    modifies ;

procedure ULTIMATE.init() returns ();
    modifies ;
    modifies ;

procedure ULTIMATE.start() returns ();
    modifies ;
    modifies ;

