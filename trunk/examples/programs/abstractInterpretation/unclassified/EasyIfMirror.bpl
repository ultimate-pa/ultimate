//#Safe
procedure EasyIf() 
{
	var x: int;
	havoc x;
	if (!(0<x)) {
		assert(x <= 0);
	}
}