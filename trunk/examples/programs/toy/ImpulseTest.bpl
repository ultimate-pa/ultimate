//#Safe
//author: nutz
//toy example that exposes a problem with the simple redirecting strategy in the impulse algorithm
procedure foo() {
	var x,y,a,f:int;
	x:=0;
	y:=0;
	
	while(*)
	{
		if(f==0)
		{
			while (*) {
				a:=a+1;
			}
			x:=x+1;
		} else {
			while (*) {
				a:=a+1;
			}
			y:=y+1;
		}
	}
	assert(x!=-1 && y!=-1);
}
