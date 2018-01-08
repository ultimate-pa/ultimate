//#Unsafe
/*
 * test for loop detection
 * 
 * Author: ben.biesenbach@gmx.de
 *
 */

procedure main()
{
  var x: int;
  x := 0;
  while (x < 2000){
    x := x + 1;
    assert (x < 1500);
  }
}

/*Loop to "mainFINAL"
 *(exists ((n Int)) 
 *	(and 
 *		(forall ((j Int)) 
 *			(xor 
 *				(>= j n)
 *				(or 
 *					(< j 0) 
 *					(< (+ x_2 j) 20)
 *				)
 *			)
 *		) 
 *		(forall ((k Int)) 
 *			(xor 
 *				(>= k n) 
 *				(or 
 *					(and 
 *						(< (+ x_2 k) 20)
 *						(= x_3 (+ x_2 k 1)) 
 *						(< x_3 25)
 *					) 
 *					(< k 0)
 *				)
 *			)
 *		) 
 *		(= x_3 (+ x_2 n))
 *	)
 *)
 *
 *Loop to "mainErr0AssertViolation"
 *(exists ((n Int)) 
 *	(and 
 *		(forall ((j Int)) 
 *			(xor 
 *				(>= j n) 
 *				(or 
 *					(< j 0)
 *					(and
 *						(= x_3 (+ x_2 j 1))
 *						(< x_3 25)
 *					)
 *				)
 *			)
 *		)
 *		(forall ((k Int)) 
 *			(xor 
 *				(>= k n) 
 *				(or 
 *					(< k 0) 
 *					(and 
 *						(< (+ x_2 k) 20)
 *						(= x_3 (+ x_2 k 1))
 *						(< x_3 25)
 *					)
 *				)
 *			)
 *		) 
 *		(= x_3 (+ x_2 n))
 *	)
 *)
 */