//#Safe
procedure EasyIf() 
{
	var x: int;
	havoc x;
	if (!(x>0)) {
		assert(x <= 0);
	}
}