var  x,s: int;

procedure ULTIMATE.start() returns ()
modifies x,s;
{	
 x := 0;
  while(true)
  {
	havoc x;
  	s:=0;
  	if(x > 42){
  		s:= 1;
    } 
	if (x = 44){
  		s:= 0;
  	}
	if (x = 55){
  		s:= 0;
  	}
	if (x = 66){
  		s:= 0;
  	}
	if (x = 77){
  		s:= 0;
  	}
	
  }
}