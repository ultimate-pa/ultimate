//#Safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-08-30
 * 
 * In Boogie the result of equality and comparison operators has type bool.
 * In C the type is int.
 * We use (b ? 1 : 0) to convert an bool in Boogie to an in int.
 * We do this conversion of demand.
 */


int main() {
	/* in expression */
	int a = 1 + ( 13 > 7);
	//@ assert a == 2;
	
	/* on assignment */
	int b;
	b =  ( 13 > 7);
	//@ assert b == 1;
	
	/* on assignment */
	int b = ( 13 > 7);
	//@ assert b == 1;
	
	
	return 0;
}