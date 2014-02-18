implementation main() returns (#res : int)
{
    var ~s~1.a : int;

  $Ultimate##0:
    ~s~1.a := 5;
    return;
}

var ~struct1instance.a : int;
implementation ULTIMATE.init() returns ()
{
  $Ultimate##0:
    ~struct1instance.a := 0;
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

procedure main() returns (#res : int);
    modifies ;

procedure ULTIMATE.init() returns ();
    modifies ~struct1instance.a;
    modifies ;

procedure ULTIMATE.start() returns ();
    modifies ~struct1instance.a;
    modifies ;

