//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2020-04-16
 * 
 * Program that has the simple loop invariant
 * y == z && y != 0
 * but we will only find a loop invariant with few quantifiers
 * if we use our PolynomialRelation instead of our
 * AffineRelation.
 */



var x, y, z : int;

procedure main() returns ();
modifies y, x;

implementation main() returns (){
    assume x*x == x * (1 + x);
	y := z * (1 + x);
	assume y != 0;
    while(*){}
    havoc x;
    assume y == z * (1 + x);
    assert x*x == x * (1 + x);
}

