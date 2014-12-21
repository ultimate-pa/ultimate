var mad: bool;
var warn:bool;

procedure main() returns()
modifies mad, warn;
{
  var t, tn: int;
  
  call warn();
  while(true){
    havoc tn;
    call t:= calcTemp(tn);
    if(t > 13){
	    call warn();
    } else {
      call unwarn();
    }
  }
}

procedure calcTemp(a:int) returns(b:int)
{
	b:= a-10;
}

procedure warn() returns()
modifies warn, mad;
{
  warn := true;
  mad := true;
}

procedure unwarn() returns()
modifies warn;
{
  warn := false;
  //mad := true; // bug
}

