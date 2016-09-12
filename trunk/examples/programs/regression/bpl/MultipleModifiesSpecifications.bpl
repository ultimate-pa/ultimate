// #Unsafe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-09-09
 *
 */

var x: int;
var y: int;

implementation main() returns (){
	x := 1;
	y := 1;
	assert (x == old(x) || y == old(y));

}

procedure main() returns ();
modifies x,y;


