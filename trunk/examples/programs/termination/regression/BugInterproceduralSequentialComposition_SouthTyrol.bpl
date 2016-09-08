//#nonterminating
/*
 * Date: 2016-09-07
 * Author: Matthias Heizmann
 * 
 */

implementation ULTIMATE.start() returns (){

    call hill(0);
}

implementation mountain() returns (){

    while (true)
    {
    }
    return;
}

implementation hill(x : int) returns (){
    call mountain();
}


procedure mountain() returns ();
modifies ;

procedure hill(x : int) returns ();
modifies ;


procedure ULTIMATE.start() returns ();

