/* #Unsafe */
/* Author: Markus Lindenmann */
/* Date: September 2012 */
// Matthias: Maybe we need something to deal with division

implementation meth() returns ()
{
     var i~1 : int;
     var j~1 : int;
     var k~1 : int;
     var l~1 : int;
     var divZero~1 : int;

     i~1 := 0;
     i~1 := 0;
     i~1 := 0;
     i~1 := -58;
     i~1 := 456789;
     i~1 := 4;
     i~1 := -154;
     j~1 := 0;
     k~1 := 0;
     l~1 := 3;
     assert 0 != 0;
     divZero~1 := i~1 / 0;
     assert 0 != j~1;
     divZero~1 := i~1 / j~1;
}

procedure meth() returns ();
     modifies ;

procedure ~init() returns ();
     modifies ;

implementation ~init() returns ()
{
}