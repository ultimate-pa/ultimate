//#Safe
/*
 * In his master thesis, Markus Lindenmann extended Boogie by structs.
 * This example file illustrates his extension.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2018-10-03
 * 
 */


// introduce a new type 'complex' whose elements are structs
// that have two fields. The first field is called 'realPart'
// the second field is called 'imaginaryPart'.
type complex = { realPart : real, imaginaryPart : real };

procedure main()
{
	var c : complex;
	// The global type definition is conveniant but not neccessary,
	// we can also specify the type directly
	var d : { realPart : real, imaginaryPart : real };
	var i : complex;
	
	// initialize c by initializing both fields
	// we access a field by using the bang operator (!)
	c!realPart := -3.4;
	c!imaginaryPart := 5.3;
	
	// initialize d
	d!realPart := 3.4;
	d!imaginaryPart := -4.3;
	
	call i := add(c, d);
	
	assert i!realPart == 0.0;
	assert i!imaginaryPart == 1.0;
	
	
}

procedure add(a : { realPart : real, imaginaryPart : real }, b : { realPart : real, imaginaryPart : real }) returns(res : { realPart : real, imaginaryPart : real })
{
	res!realPart := a!realPart + b!realPart;
	res!imaginaryPart := a!imaginaryPart + b!imaginaryPart;
}
