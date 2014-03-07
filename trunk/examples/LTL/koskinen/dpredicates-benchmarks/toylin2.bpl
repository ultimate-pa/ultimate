// Based on benchmark toylin2.c
// manually translated by DD
// [DD] Ultimate LTL Model Checker Property: 
// x U (!x && (a -> <>b))
// a: c > (servers / 2)
// b: resp > (servers / 2)
// x: init = 0
// [/DD]
// additional comments: 
// * c was an unsigned int 
// * init is new and necessary to state that the property should only be analysed after init 
var c,servers,resp,curr_serv,serversdiv2 : int;
var init : int;

procedure init() 
modifies c,servers,resp,curr_serv,serversdiv2;
{
  havoc c; 
  assume(c>0);
  havoc servers; 
  assume(servers>0);
  havoc serversdiv2;
  if(*){
    assume(serversdiv2+serversdiv2==servers);
	}
  else{
    assume(serversdiv2+serversdiv2+1==servers);
	}
  resp := 0;
  curr_serv := servers;
}

procedure body() 
modifies c,curr_serv,resp;
{
  var ddd : int; 
  
  while(curr_serv > 0) {
    if(*) {
      c := c - 1; 
	  curr_serv := curr_serv - 1 ;
      resp := resp + 1 ;
    } else 
	{
      assume(c < curr_serv);
      curr_serv := curr_serv - 1;
    }
  }
  while(true) { 
	ddd:=ddd; 
  }
}

procedure ULTIMATE.start() 
modifies c,servers,resp,curr_serv,serversdiv2,init;
{
	init := 0;
	call init();
	init := 1;
	call body();
}
