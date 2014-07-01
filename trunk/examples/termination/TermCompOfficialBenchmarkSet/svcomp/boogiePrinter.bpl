implementation main() returns (main : int)
{
    var ~n~2 : int;
    var ~x~2 : int;
    var ~y~2 : int;
    var #t~nondet0 : int;
    var #t~nondet1 : int;
    var #t~nondet2 : int;
    var #t~post4 : int;
    var #t~nondet3 : int;
    var #t~post5 : int;
    var #t~post7 : int;
    var #t~nondet6 : int;

    ~n~2 := #t~nondet0;
    havoc #t~nondet0;
    ~x~2 := #t~nondet1;
    havoc #t~nondet1;
    ~y~2 := #t~nondet2;
    havoc #t~nondet2;
    while (true)
    {
      Loop~2:
        if (!(~x~2 >= 0)) {
            break;
        }
        while (true)
        {
          Loop~3:
            if (!(~y~2 >= 0 && #t~nondet3 != 0)) {
                havoc #t~nondet3;
                break;
            } else {
                havoc #t~nondet3;
            }
            #t~post4 := ~y~2;
            ~y~2 := #t~post4 - 1;
            havoc #t~post4;
        }
        #t~post5 := ~x~2;
        ~x~2 := #t~post5 - 1;
        havoc #t~post5;
        while (true)
        {
          Loop~3:
            if (!(~y~2 <= ~n~2 && #t~nondet6 != 0)) {
                havoc #t~nondet6;
                break;
            } else {
                havoc #t~nondet6;
            }
            #t~post7 := ~y~2;
            ~y~2 := #t~post7 + 1;
            havoc #t~post7;
        }
    }
    main := 0;
    return;
}

implementation ULTIMATE.init() returns ()
{
}

implementation ULTIMATE.start() returns ()
{
    var #t~ret8 : int;

    call ULTIMATE.init();
    call #t~ret8 := main();
}

procedure __VERIFIER_nondet_int() returns (#res : int);
    modifies ;

procedure main() returns (main : int);
    modifies ;

procedure ULTIMATE.init() returns ();
    modifies ;
    modifies ;

procedure ULTIMATE.start() returns ();
    modifies ;
    modifies ;

