//#Safe
// Extremely simple example for Boogie LTL properties 
// #LTLProperty: <>[]AP(x==0)

var x : int;

procedure main() 
modifies x;
{
	x := 10;
	while (x>0) {
		x:=x-1;
	}
}

