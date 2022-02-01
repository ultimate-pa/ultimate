var foo:bool;

procedure main() returns(bar:int)
modifies foo;
{
  
  bar := 5;
  foo:= false;
  call bar := main();
  if(foo)
	{ bar:= 6; }
  return;
}
