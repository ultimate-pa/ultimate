//#Unsafe
/*
 * Author: Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Date: 2017-06-14
 */

implementation main() returns (){
    call init();
    assert false;
}

implementation init() returns (){
}

procedure main() returns ();
modifies ;
procedure init() returns ();
modifies ;