//#Safe
/*
 * test for loop detection
 * 
 * Author: ben.biesenbach@gmx.de
 *
 */

procedure main() {
	var x : int;
	x := 501;
	while (x < 1000) {
		x := x + 2;
	}
	assert (x == 1001);
}

/*
 * Fail:
 *
 * assert (x == 1001);
 * assert (x > 1000);
 * assert (x >= 1001);
 * assert (x < 1002);
 * assert (x > 1000 && x < 1002);
 * assert (x == 1001 || x == 1002);
 * assert (x == 1001 || x == 1000);
 *
 * Succsess:
 *
 * assert (x > 999);
 * assert (x >= 1000);
 * assert (x < 1003);
 * assert (x <= 1002);
 *
 * assert (x == 1000 || x == 1001 || x == 1002);
 * assert (x > 999 && x < 1003);
 * assert (x >= 1001 || x < 1002);
 *
 */

/*
 *(exists ((n Int)) 
 *	(and 
 *		(forall ((j Int)) 
 *			(xor 
 *				(>= j n) 
 *				(or 
 *					(< j 0) 
 *					(< (+ x_2 (* 2.0 j)) 1000)
 *				)
 *			)
 *		)
 *	(= x_3 (+ x_2 (* 2.0 n)))
 *	)
 *)
 *
 */