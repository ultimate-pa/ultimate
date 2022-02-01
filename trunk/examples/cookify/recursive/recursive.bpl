var foo:bool;

procedure main() returns()
modifies foo;
{
  var bla:int;
  call bla := recursive(0);
  return;
}

procedure recursive(i: int) returns(v : int)
modifies foo;
{
  goto lif, lelse;
  lelse:
  assume i == 102;
  call v := recursive(i+1); 
  foo:= true;
  return;
  lif:
  assume i < 100;
  call v := recursive(i+1); 
  foo:= false;
  return;
  
  v:= 1;
  return;
}
