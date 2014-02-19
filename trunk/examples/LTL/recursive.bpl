/*
Working Example with either:

		String fileContent = "[]( x -> <> y )\n"
		+ "x: a > 55 \n"
		+ "y: a = 2";
		
or for a not fitting property

		String fileContent = "[]( x -> <> y )\n"
		+ "x: a > 42 \n"
		+ "y: a = 2";
*/

var a:int;

procedure ULTIMATE.start() returns()
modifies a;
{
  havoc a;
  if (a > 42) {
	call a := recursive(a);
  }
  return;
}

procedure recursive(i: int) returns(v : int)
{ 
  v:= 2;
  return;
}
