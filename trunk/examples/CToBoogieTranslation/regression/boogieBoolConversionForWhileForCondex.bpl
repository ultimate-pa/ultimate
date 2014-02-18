implementation foo() returns (#res : int)
{
  $Ultimate##0:
    #res := 0;
    return;
}

implementation main() returns (#res : int)
{
    var ~a~2 : int;
    var #t~ret0 : int;
    var #t~ret2 : int;
    var #t~post1 : int;
    var ~n~4 : int;
    var #t~ite3 : int;

  $Ultimate##0:
    ~a~2 := 1;
    goto $Ultimate##1;
  $Ultimate##1:
    goto $Ultimate##2, $Ultimate##3;
  $Ultimate##2:
    assume true;
    goto $Ultimate##4, $Ultimate##5;
  $Ultimate##4:
    assume !(~a~2 != 0);
    goto $Ultimate##6;
  $Ultimate##5:
    assume !!(~a~2 != 0);
    call #t~ret0 := foo();
    havoc #t~ret0;
    goto $Ultimate##1;
  $Ultimate##3:
    assume !true;
    goto $Ultimate##6;
  $Ultimate##6:
    ~n~4 := 1;
    goto $Ultimate##7;
  $Ultimate##7:
    goto $Ultimate##8, $Ultimate##9;
  $Ultimate##8:
    assume true;
    goto $Ultimate##10, $Ultimate##11;
  $Ultimate##10:
    assume !(~n~4 < 10);
    goto $Ultimate##12;
  $Ultimate##11:
    assume !!(~n~4 < 10);
    call #t~ret2 := foo();
    havoc #t~ret2;
    #t~post1 := ~n~4 + 1;
    ~n~4 := #t~post1;
    havoc #t~post1;
    goto $Ultimate##7;
  $Ultimate##9:
    assume !true;
    goto $Ultimate##12;
  $Ultimate##12:
    goto $Ultimate##13, $Ultimate##14;
  $Ultimate##13:
    assume ~a~2 != 0;
    #t~ite3 := 1;
    goto $Ultimate##15;
  $Ultimate##14:
    assume !(~a~2 != 0);
    #t~ite3 := 0;
    goto $Ultimate##15;
  $Ultimate##15:
    ~a~2 := #t~ite3;
    havoc #t~ite3;
    return;
}

implementation ULTIMATE.init() returns ()
{
  $Ultimate##0:
    return;
}

implementation ULTIMATE.start() returns ()
{
    var #t~ret4 : int;

  $Ultimate##0:
    call ULTIMATE.init();
    call #t~ret4 := main();
    return;
}

procedure foo() returns (#res : int);
    modifies ;

procedure main() returns (#res : int);
    modifies ;

procedure ULTIMATE.init() returns ();
    modifies ;
    modifies ;

procedure ULTIMATE.start() returns ();
    modifies ;
    modifies ;

