//#Safe
/*
 * 2017-11-20 DD
 * 
 * Old Vars have to be assigned even if they are only read 
 *
 */

var SIZE : int;

procedure ULTIMATE.init() returns ()
modifies SIZE;
{
    SIZE := 0;
}

procedure ULTIMATE.start() returns ()
modifies SIZE;
{
    call ULTIMATE.init();
    call main();
}

procedure foo(x : int) returns (#res : int)
modifies ;
{
    var j : int;
    j := 0;
    while (j < 1)
    {
      j := j + 1;
    }
    if (j < SIZE) {
        #res := 0;
    } else {
        #res := 1;
    }
}

procedure main() returns ()
modifies SIZE;
{
    var #t~ret1 : int;

    SIZE := 2;
    call #t~ret1 := foo(0);
    if (#t~ret1 != 0) {
        assert false;
    } 
}



